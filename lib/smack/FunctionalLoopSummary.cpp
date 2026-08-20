//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/FunctionalLoopSummary.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include <limits>

namespace smack {

using namespace llvm;

namespace {

bool getIterationCount(Loop &L, ScalarEvolution &SE, IntegerType *Ty,
                       bool IncludeFinalExitingBlock, const Value *&Count) {
  const SCEV *S = SE.getExitCount(&L, L.getExitingBlock());
  if (isa<SCEVCouldNotCompute>(S) || S->getType() != Ty)
    return false;

  if (IncludeFinalExitingBlock) {
    // SCEV's exit count is the number of backedges taken.  When the store
    // executes before the exit test (the form produced by LoopRotate), its
    // execution count is one greater.  Let SCEV simplify forms such as
    // `(N - 1) + 1` back to the original loop-invariant N.  An unsimplified
    // addition remains outside the deliberately narrow count representation.
    if (auto *C = dyn_cast<SCEVConstant>(S))
      if (C->getAPInt().isAllOnes())
        return false;
    S = SE.getAddExpr(S, SE.getOne(Ty));
  }

  if (auto *C = dyn_cast<SCEVConstant>(S))
    Count = C->getValue();
  else if (auto *U = dyn_cast<SCEVUnknown>(S))
    Count = U->getValue();
  else
    return false;

  return Count->getType() == Ty && L.isLoopInvariant(Count);
}

bool hasOnlySimpleHeaderPhis(Loop &L, const PHINode *Induction) {
  BasicBlock *Incoming = nullptr;
  BasicBlock *Backedge = nullptr;
  if (!L.getIncomingAndBackEdge(Incoming, Backedge))
    return false;

  for (Instruction &I : *L.getHeader()) {
    auto *Phi = dyn_cast<PHINode>(&I);
    if (!Phi)
      break;
    if (Phi == Induction)
      continue;

    Value *Start = Phi->getIncomingValueForBlock(Incoming);
    Value *Update = Phi->getIncomingValueForBlock(Backedge);
    if (!L.isLoopInvariant(Start) || Update->getType() != Phi->getType())
      return false;

    if (auto *BO = dyn_cast<BinaryOperator>(Update)) {
      const Value *Step = nullptr;
      if (BO->getOpcode() == Instruction::Add) {
        if (BO->getOperand(0) == Phi)
          Step = BO->getOperand(1);
        else if (BO->getOperand(1) == Phi)
          Step = BO->getOperand(0);
      } else if (BO->getOpcode() == Instruction::Sub &&
                 BO->getOperand(0) == Phi) {
        Step = BO->getOperand(1);
      }
      if (!Step || !L.isLoopInvariant(Step))
        return false;
      continue;
    }

    auto *GEP = dyn_cast<GetElementPtrInst>(Update);
    if (!GEP || GEP->getPointerOperand() != Phi)
      return false;
    for (const Use &Index : GEP->indices())
      if (!L.isLoopInvariant(Index.get()))
        return false;
  }
  return true;
}

PHINode *getUnitInduction(Loop &L, ScalarEvolution &SE,
                          PHINode *Phi) {
  // Ask LoopInfo to identify the canonical 0,+1 recurrence before querying
  // ScalarEvolution. Large generated programs can carry unrelated header
  // PHIs with deeply cyclic value graphs; LLVM 14 may recurse until it
  // segfaults merely trying to build a SCEV for one of those PHIs. Candidate
  // loops are canonical by contract, so this is both a conservative filter
  // and a way to keep SCEV focused on the semantic induction variable.
  auto *AR = dyn_cast<SCEVAddRecExpr>(SE.getSCEV(Phi));
  if (!AR || AR->getLoop() != &L || !AR->isAffine())
    return nullptr;
  auto *Start = dyn_cast<SCEVConstant>(AR->getStart());
  auto *Step = dyn_cast<SCEVConstant>(AR->getStepRecurrence(SE));
  if (!Phi->getType()->isIntegerTy() || !Start ||
      !Start->getAPInt().isZero() || !Step || !Step->getAPInt().isOne())
    return nullptr;
  return Phi;
}

bool getAffineAccess(const Value *Pointer, Loop &L, ScalarEvolution &SE,
                     AffineLoopAccess &Access) {
  auto *AR = dyn_cast<SCEVAddRecExpr>(SE.getSCEV(const_cast<Value *>(Pointer)));
  auto *GEP = dyn_cast<GetElementPtrInst>(Pointer);
  if (!AR || AR->getLoop() != &L || !AR->isAffine() ||
      (!AR->hasNoSelfWrap() && !(GEP && GEP->isInBounds())))
    return false;

  auto *Step = dyn_cast<SCEVConstant>(AR->getStepRecurrence(SE));
  if (!Step || !Step->getAPInt().isStrictlyPositive() ||
      Step->getAPInt().getActiveBits() > 64)
    return false;

  const SCEVUnknown *BaseSCEV = dyn_cast<SCEVUnknown>(AR->getStart());
  uint64_t Offset = 0;
  if (!BaseSCEV) {
    auto *Start = dyn_cast<SCEVAddExpr>(AR->getStart());
    if (!Start)
      return false;
    for (const SCEV *Operand : Start->operands()) {
      if (auto *Unknown = dyn_cast<SCEVUnknown>(Operand)) {
        if (BaseSCEV)
          return false;
        BaseSCEV = Unknown;
      } else if (auto *Constant = dyn_cast<SCEVConstant>(Operand)) {
        const APInt &Value = Constant->getAPInt();
        if (Value.isNegative() || Value.getActiveBits() > 64 ||
            Offset >
                std::numeric_limits<uint64_t>::max() - Value.getZExtValue())
          return false;
        Offset += Value.getZExtValue();
      } else {
        return false;
      }
    }
  }
  if (!BaseSCEV)
    return false;

  const Value *Base = BaseSCEV->getValue();
  if (!Base->getType()->isPointerTy() || !L.isLoopInvariant(Base))
    return false;

  Access.base = Base;
  Access.offset = Offset;
  Access.stride = Step->getAPInt().getZExtValue();
  return Access.stride != 0;
}

const AffineLoopAccess *findLoadAccess(const FunctionalLoopSummary &Summary,
                                       const LoadInst *Load) {
  for (const auto &L : Summary.loads)
    if (L.load == Load)
      return &L.access;
  return nullptr;
}

bool isSamePointwiseAccess(const AffineLoopAccess &Write,
                           const AffineLoopAccess &Read) {
  return Write.base == Read.base && Write.offset == Read.offset &&
         Write.stride == Read.stride;
}

uint64_t greatestCommonDivisor(uint64_t A, uint64_t B) {
  while (B != 0) {
    uint64_t Remainder = A % B;
    A = B;
    B = Remainder;
  }
  return A;
}

bool finiteAffineImagesAreDisjoint(const AffineLoopAccess &A,
                                   const AffineLoopAccess &B,
                                   const Value *IterationCount) {
  auto *Count = dyn_cast<ConstantInt>(IterationCount);
  if (!Count || Count->getValue().getActiveBits() > 64)
    return false;

  uint64_t Iterations = Count->getZExtValue();
  if (Iterations == 0)
    return true;

  auto LastOffset = [Iterations](const AffineLoopAccess &Access,
                                 uint64_t &Last) {
    uint64_t Steps = Iterations - 1;
    if (Steps >
        (std::numeric_limits<uint64_t>::max() - Access.offset) / Access.stride)
      return false;
    Last = Access.offset + Steps * Access.stride;
    return true;
  };

  uint64_t LastA = 0;
  uint64_t LastB = 0;
  return LastOffset(A, LastA) && LastOffset(B, LastB) &&
         (LastA < B.offset || LastB < A.offset);
}

bool areAffineAccessesDisjoint(const AffineLoopAccess &A,
                               const AffineLoopAccess &B,
                               const Value *IterationCount) {
  if (A.base != B.base)
    return false;
  if (finiteAffineImagesAreDisjoint(A, B, IterationCount))
    return true;
  uint64_t Difference =
      A.offset >= B.offset ? A.offset - B.offset : B.offset - A.offset;
  return Difference % greatestCommonDivisor(A.stride, B.stride) != 0;
}

bool validateRhs(const Value *V, FunctionalLoopSummary &Summary,
                 ScalarEvolution &SE, AAResults &AA, MemorySSA &MSSA,
                 DominatorTree &DT) {
  if (isa<Constant>(V) || V == Summary.induction)
    return true;

  auto *I = dyn_cast<Instruction>(V);
  if (!I || !Summary.loop->contains(I))
    return Summary.loop->isLoopInvariant(V);

  if (I->getType() == Summary.iterationType) {
    if (auto *AR = dyn_cast<SCEVAddRecExpr>(
            SE.getSCEV(const_cast<Instruction *>(I)))) {
      auto *Start = dyn_cast<SCEVConstant>(AR->getStart());
      auto *Step = dyn_cast<SCEVConstant>(AR->getStepRecurrence(SE));
      if (AR->getLoop() == Summary.loop && AR->isAffine() && Start && Step) {
        for (const auto &Recurrence : Summary.recurrences)
          if (Recurrence.value == V)
            return true;
        Summary.recurrences.push_back({V, Start->getValue(), Step->getValue()});
        return true;
      }
    }
  }

  if (auto *Load = dyn_cast<LoadInst>(I)) {
    if (!Load->isSimple())
      return false;
    if (findLoadAccess(Summary, Load))
      return true;

    AffineLoopAccess Read;
    if (!getAffineAccess(Load->getPointerOperand(), *Summary.loop, SE, Read))
      return false;

    // Every store must either be on a distinct object, denote the load's same
    // pointwise address, or have an affine image disjoint from the load's
    // image.  These are all-iterations proofs; a same-iteration alias query
    // would be insufficient.
    const Value *ReadObject = getUnderlyingObject(Read.base);
    bool UsesRecurrenceProof = false;
    for (const auto &Write : Summary.stores) {
      const Value *WriteObject = getUnderlyingObject(Write.access.base);
      if (AA.isNoAlias(WriteObject, ReadObject))
        continue;
      bool SamePointwise = isSamePointwiseAccess(Write.access, Read);
      if (SamePointwise && !DT.dominates(Load, Write.store))
        return false;
      if (!SamePointwise &&
          !areAffineAccessesDisjoint(Write.access, Read,
                                     Summary.iterationCount))
        return false;
      UsesRecurrenceProof = true;
    }

    auto *MA = MSSA.getMemoryAccess(Load);
    if (!MA)
      return false;
    MemoryAccess *Clobber = MSSA.getWalker()->getClobberingMemoryAccess(MA);
    // A same-object load normally reaches the loop MemoryPhi.  The recurrence
    // proofs above discharge that may-clobber; reads separated only by AA must
    // independently reach entry memory.
    if (!UsesRecurrenceProof && !MSSA.isLiveOnEntryDef(Clobber) &&
        Summary.loop->contains(Clobber->getBlock()))
      return false;

    Summary.loads.push_back({Load, Read});
    return true;
  }

  if (auto *BO = dyn_cast<BinaryOperator>(I)) {
    switch (BO->getOpcode()) {
    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::Mul:
      return validateRhs(BO->getOperand(0), Summary, SE, AA, MSSA, DT) &&
             validateRhs(BO->getOperand(1), Summary, SE, AA, MSSA, DT);
    case Instruction::UDiv:
    case Instruction::URem: {
      auto *Divisor = dyn_cast<ConstantInt>(BO->getOperand(1));
      return Divisor && !Divisor->isZero() &&
             validateRhs(BO->getOperand(0), Summary, SE, AA, MSSA, DT);
    }
    case Instruction::SDiv:
    case Instruction::SRem: {
      auto *Divisor = dyn_cast<ConstantInt>(BO->getOperand(1));
      return Divisor && !Divisor->isZero() && !Divisor->isMinusOne() &&
             validateRhs(BO->getOperand(0), Summary, SE, AA, MSSA, DT);
    }
    default:
      return false;
    }
  }

  if (auto *Cast = dyn_cast<CastInst>(I)) {
    switch (Cast->getOpcode()) {
    case Instruction::Trunc:
    case Instruction::ZExt:
    case Instruction::SExt:
    case Instruction::BitCast:
      return Cast->getType()->isIntegerTy() &&
             Cast->getOperand(0)->getType()->isIntegerTy() &&
             validateRhs(Cast->getOperand(0), Summary, SE, AA, MSSA, DT);
    default:
      return false;
    }
  }

  if (auto *Cmp = dyn_cast<ICmpInst>(I))
    return validateRhs(Cmp->getOperand(0), Summary, SE, AA, MSSA, DT) &&
           validateRhs(Cmp->getOperand(1), Summary, SE, AA, MSSA, DT);

  if (auto *Select = dyn_cast<SelectInst>(I))
    return validateRhs(Select->getCondition(), Summary, SE, AA, MSSA, DT) &&
           validateRhs(Select->getTrueValue(), Summary, SE, AA, MSSA, DT) &&
           validateRhs(Select->getFalseValue(), Summary, SE, AA, MSSA, DT);

  return false;
}

struct SupportedControlFlow {
  const BranchInst *bodyCondition = nullptr;
  const BasicBlock *merge = nullptr;
};

bool hasSupportedControlFlow(Loop &L, SupportedControlFlow &Flow) {
  BasicBlock *Exiting = L.getExitingBlock();
  auto *ExitBranch =
      Exiting ? dyn_cast<BranchInst>(Exiting->getTerminator()) : nullptr;
  if (!ExitBranch || !ExitBranch->isConditional())
    return false;

  bool HasLoopSuccessor = false;
  bool HasExitSuccessor = false;
  for (BasicBlock *Successor : ExitBranch->successors()) {
    HasLoopSuccessor |= L.contains(Successor);
    HasExitSuccessor |= !L.contains(Successor);
  }
  if (!HasLoopSuccessor || !HasExitSuccessor)
    return false;

  for (BasicBlock *BB : L.blocks()) {
    auto *Branch = dyn_cast<BranchInst>(BB->getTerminator());
    if (!Branch)
      return false;
    if (BB == Exiting)
      continue;
    if (Branch->isConditional()) {
      if (Flow.bodyCondition || !L.contains(Branch->getSuccessor(0)) ||
          !L.contains(Branch->getSuccessor(1)))
        return false;
      Flow.bodyCondition = Branch;
    } else if (!L.contains(Branch->getSuccessor(0))) {
      return false;
    }
  }

  if (Flow.bodyCondition) {
    const BasicBlock *Then = Flow.bodyCondition->getSuccessor(0);
    const BasicBlock *Else = Flow.bodyCondition->getSuccessor(1);
    auto *ThenBranch = dyn_cast<BranchInst>(Then->getTerminator());
    auto *ElseBranch = dyn_cast<BranchInst>(Else->getTerminator());
    if (ThenBranch && ThenBranch->isUnconditional() &&
        ThenBranch->getSuccessor(0) == Else) {
      Flow.merge = Else;
    } else if (ElseBranch && ElseBranch->isUnconditional() &&
               ElseBranch->getSuccessor(0) == Then) {
      Flow.merge = Then;
    } else if (ThenBranch && ElseBranch && ThenBranch->isUnconditional() &&
               ElseBranch->isUnconditional() &&
               ThenBranch->getSuccessor(0) == ElseBranch->getSuccessor(0)) {
      Flow.merge = ThenBranch->getSuccessor(0);
    } else {
      return false;
    }

    if (!L.contains(Flow.merge))
      return false;
  }
  return true;
}

bool storeExecutesBeforeExitTest(Loop &L, const StoreInst &Store,
                                 DominatorTree &DT, bool &BeforeExitTest) {
  if (Store.getParent() == L.getExitingBlock()) {
    BeforeExitTest = true;
    return true;
  }
  BeforeExitTest = !DT.dominates(L.getExitingBlock(), Store.getParent());
  return true;
}

void getStoreGuard(const StoreInst &Store, const SupportedControlFlow &Flow,
                   DominatorTree &DT, const Value *&Guard, bool &GuardValue) {
  Guard = nullptr;
  GuardValue = true;
  if (!Flow.bodyCondition)
    return;

  const BasicBlock *StoreBlock = Store.getParent();
  if (DT.dominates(Flow.merge, StoreBlock))
    return;
  for (unsigned I = 0; I < 2; ++I) {
    const BasicBlock *Successor = Flow.bodyCondition->getSuccessor(I);
    if (Successor != Flow.merge && DT.dominates(Successor, StoreBlock)) {
      Guard = Flow.bodyCondition->getCondition();
      GuardValue = I == 0;
      return;
    }
  }
}

bool hasUnsupportedEscapingValue(Loop &L, const PHINode *Induction,
                                 bool &InductionEscapes) {
  InductionEscapes = false;
  for (BasicBlock *BB : L.blocks())
    for (Instruction &I : *BB)
      if (!I.getType()->isVoidTy())
        for (User *U : I.users())
          if (auto *Use = dyn_cast<Instruction>(U))
            if (!L.contains(Use)) {
              if (&I != Induction &&
                  !(isa<PHINode>(Use) && Use->getParent() == L.getExitBlock()))
                return true;
              InductionEscapes = true;
            }
  return false;
}

bool hasOnlySupportedInstructions(Loop &L,
                                  SmallVectorImpl<const StoreInst *> &Stores) {
  for (BasicBlock *BB : L.blocks()) {
    for (Instruction &I : *BB) {
      if (isa<DbgInfoIntrinsic>(I))
        continue;
      if (auto *SI = dyn_cast<StoreInst>(&I)) {
        if (!SI->isSimple())
          return false;
        Stores.push_back(SI);
        continue;
      }
      if (isa<LoadInst>(I) || isa<PHINode>(I) || isa<BinaryOperator>(I) ||
          isa<CastInst>(I) || isa<GetElementPtrInst>(I) || isa<ICmpInst>(I) ||
          isa<SelectInst>(I) || isa<BranchInst>(I))
        continue;
      return false;
    }
  }
  return !Stores.empty();
}

bool analyzeLoop(Loop &L, ScalarEvolution &SE, AAResults &AA, MemorySSA &MSSA,
                 DominatorTree &DT, FunctionalLoopSummary &Summary) {
  SupportedControlFlow Flow;
  if (L.getParentLoop() || !L.getSubLoops().empty() ||
      !L.isLoopSimplifyForm() || L.getNumBackEdges() != 1 ||
      !L.getExitingBlock() || !L.getLoopPreheader() || !L.getLoopLatch() ||
      !L.getExitBlock() || !hasSupportedControlFlow(L, Flow))
    return false;

  PHINode *CanonicalInduction = L.getCanonicalInductionVariable();
  if (!CanonicalInduction ||
      !hasOnlySimpleHeaderPhis(L, CanonicalInduction))
    return false;
  PHINode *Induction = getUnitInduction(L, SE, CanonicalInduction);
  auto *IterationType =
      Induction ? dyn_cast<IntegerType>(Induction->getType()) : nullptr;
  if (!IterationType)
    return false;
  bool InductionEscapes = false;
  if (hasUnsupportedEscapingValue(L, Induction, InductionEscapes))
    return false;

  SmallVector<const StoreInst *, 2> Stores;
  if (!hasOnlySupportedInstructions(L, Stores))
    return false;

  const Value *IterationCount = nullptr;
  bool StoresExecuteBeforeExitTest = false;
  if (!storeExecutesBeforeExitTest(L, *Stores.front(), DT,
                                   StoresExecuteBeforeExitTest))
    return false;
  for (const StoreInst *Store : Stores) {
    bool BeforeExitTest = false;
    if (!storeExecutesBeforeExitTest(L, *Store, DT, BeforeExitTest) ||
        BeforeExitTest != StoresExecuteBeforeExitTest)
      return false;
  }
  if (!getIterationCount(L, SE, IterationType, StoresExecuteBeforeExitTest,
                         IterationCount))
    return false;

  Summary.loop = &L;
  Summary.preheader = L.getLoopPreheader();
  Summary.exit = L.getExitBlock();
  Summary.induction = Induction;
  Summary.inductionEscapes = InductionEscapes;
  Summary.iterationType = IterationType;
  Summary.iterationCount = IterationCount;

  const SCEV *IterationCountSCEV =
      SE.getSCEV(const_cast<Value *>(IterationCount));
  for (Instruction &I : *L.getExitBlock()) {
    auto *Phi = dyn_cast<PHINode>(&I);
    if (!Phi)
      break;
    if (Phi->getNumIncomingValues() != 1 ||
        !L.contains(Phi->getIncomingBlock(0)) ||
        SE.getSCEVAtScope(Phi->getIncomingValue(0), L.getParentLoop()) !=
            IterationCountSCEV)
      return false;
    Summary.finalInductionPhis.push_back(Phi);
  }

  for (const StoreInst *Store : Stores) {
    AffineLoopAccess Write;
    if (!getAffineAccess(Store->getPointerOperand(), L, SE, Write))
      return false;
    const Value *Guard = nullptr;
    bool GuardValue = true;
    getStoreGuard(*Store, Flow, DT, Guard, GuardValue);
    Summary.stores.push_back({Store, Write, Guard, GuardValue});
  }

  // Every iteration must own a distinct destination for every store, and the
  // affine images of separate stores must not overlap each other.
  for (unsigned I = 0; I < Summary.stores.size(); ++I)
    for (unsigned J = I + 1; J < Summary.stores.size(); ++J) {
      const auto &A = Summary.stores[I].access;
      const auto &B = Summary.stores[J].access;
      bool MutuallyExclusive =
          isSamePointwiseAccess(A, B) && Summary.stores[I].guard &&
          Summary.stores[I].guard == Summary.stores[J].guard &&
          Summary.stores[I].guardValue != Summary.stores[J].guardValue;
      if (!AA.isNoAlias(getUnderlyingObject(A.base),
                        getUnderlyingObject(B.base)) &&
          !areAffineAccessesDisjoint(A, B, Summary.iterationCount) &&
          !MutuallyExclusive)
        return false;
    }

  for (const auto &Store : Summary.stores) {
    if (Store.guard && !validateRhs(Store.guard, Summary, SE, AA, MSSA, DT))
      return false;
    if (!validateRhs(Store.store->getValueOperand(), Summary, SE, AA, MSSA, DT))
      return false;
  }
  return true;
}

} // namespace

std::vector<FunctionalLoopSummary>
FunctionalLoopSummaryAnalysis::analyze(Function &F, LoopInfo &LI,
                                       ScalarEvolution &SE, AAResults &AA,
                                       MemorySSA &MSSA) {
  std::vector<FunctionalLoopSummary> Result;
  DominatorTree DT(F);
  for (Loop *L : LI.getLoopsInPreorder()) {
    FunctionalLoopSummary Summary;
    if (analyzeLoop(*L, SE, AA, MSSA, DT, Summary))
      Result.push_back(std::move(Summary));
  }
  return Result;
}

} // namespace smack
