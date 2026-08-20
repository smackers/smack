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
#include <set>

namespace smack {

using namespace llvm;

namespace {

bool isSupportedInvariantSCEV(const SCEV *S, Loop &L, ScalarEvolution &SE) {
  if (!S->getType()->isIntegerTy() || !SE.isLoopInvariant(S, &L))
    return false;
  if (isa<SCEVConstant>(S))
    return true;
  if (auto *Unknown = dyn_cast<SCEVUnknown>(S))
    return L.isLoopInvariant(Unknown->getValue());
  if (auto *Cast = dyn_cast<SCEVCastExpr>(S))
    return isSupportedInvariantSCEV(Cast->getOperand(), L, SE);
  if (auto *NAry = dyn_cast<SCEVNAryExpr>(S)) {
    if (!isa<SCEVAddExpr>(NAry) && !isa<SCEVMulExpr>(NAry))
      return false;
    for (const SCEV *Operand : NAry->operands())
      if (!isSupportedInvariantSCEV(Operand, L, SE))
        return false;
    return true;
  }
  if (auto *Div = dyn_cast<SCEVUDivExpr>(S)) {
    auto *Divisor = dyn_cast<SCEVConstant>(Div->getRHS());
    return Divisor && !Divisor->getAPInt().isZero() &&
           isSupportedInvariantSCEV(Div->getLHS(), L, SE);
  }
  return false;
}

bool getIterationCount(Loop &L, BasicBlock *ExitingBlock, ScalarEvolution &SE,
                       IntegerType *Ty, bool IncludeFinalExitingBlock,
                       const SCEV *&Count) {
  const SCEV *S = SE.getExitCount(&L, ExitingBlock);
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

  if (!isSupportedInvariantSCEV(S, L, SE))
    return false;
  Count = S;
  return Count->getType() == Ty;
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

PHINode *getSimplePositiveInductionCandidate(Loop &L) {
  BasicBlock *Incoming = nullptr;
  BasicBlock *Backedge = nullptr;
  if (!L.getIncomingAndBackEdge(Incoming, Backedge))
    return nullptr;

  PHINode *Candidate = nullptr;
  for (Instruction &I : *L.getHeader()) {
    auto *Phi = dyn_cast<PHINode>(&I);
    if (!Phi)
      break;
    if (!Phi->getType()->isIntegerTy() ||
        !L.isLoopInvariant(Phi->getIncomingValueForBlock(Incoming)))
      continue;
    auto *Update =
        dyn_cast<BinaryOperator>(Phi->getIncomingValueForBlock(Backedge));
    if (!Update || Update->getOpcode() != Instruction::Add)
      continue;
    const Value *Step = nullptr;
    if (Update->getOperand(0) == Phi)
      Step = Update->getOperand(1);
    else if (Update->getOperand(1) == Phi)
      Step = Update->getOperand(0);
    auto *ConstantStep = dyn_cast_or_null<ConstantInt>(Step);
    if (!ConstantStep || !ConstantStep->getValue().isStrictlyPositive())
      continue;
    if (Candidate)
      return nullptr;
    Candidate = Phi;
  }
  return Candidate;
}

PHINode *getPositiveInduction(Loop &L, ScalarEvolution &SE, PHINode *Phi,
                              const Value *&Initial,
                              const ConstantInt *&StepValue) {
  // Ask LoopInfo to identify the canonical 0,+1 recurrence before querying
  // ScalarEvolution. Large generated programs can carry unrelated header
  // PHIs with deeply cyclic value graphs; LLVM 14 may recurse until it
  // segfaults merely trying to build a SCEV for one of those PHIs. Candidate
  // loops are canonical by contract, so this is both a conservative filter
  // and a way to keep SCEV focused on the semantic induction variable.
  auto *AR = dyn_cast<SCEVAddRecExpr>(SE.getSCEV(Phi));
  if (!AR || AR->getLoop() != &L || !AR->isAffine())
    return nullptr;
  auto *Step = dyn_cast<SCEVConstant>(AR->getStepRecurrence(SE));
  BasicBlock *Incoming = nullptr;
  BasicBlock *Backedge = nullptr;
  if (!Phi->getType()->isIntegerTy() || !Step ||
      !Step->getAPInt().isStrictlyPositive() ||
      !L.getIncomingAndBackEdge(Incoming, Backedge))
    return nullptr;
  Initial = Phi->getIncomingValueForBlock(Incoming);
  if (Initial->getType() != Phi->getType() || !L.isLoopInvariant(Initial) ||
      AR->getStart() != SE.getSCEV(const_cast<Value *>(Initial)))
    return nullptr;
  StepValue = Step->getValue();
  return Phi;
}

bool getAffineAccess(const Value *Pointer, Loop &L, ScalarEvolution &SE,
                     const PHINode *Induction, AffineLoopAccess &Access) {
  const SCEV *PointerSCEV = SE.getSCEV(const_cast<Value *>(Pointer));
  auto *AR = dyn_cast<SCEVAddRecExpr>(PointerSCEV);
  auto *GEP = dyn_cast<GetElementPtrInst>(Pointer);
  const SCEV *Start = AR ? AR->getStart() : nullptr;

  // A narrower integer induction used as a pointer index is commonly exposed
  // by LLVM 14 as `base + zext({0,+,1}<L>)`, rather than a pointer AddRec.
  // Accept only the cast of this loop's already-validated zero,+1 induction;
  // broader casted recurrences need a separate no-wrap proof.
  if (!AR && Induction && GEP && GEP->isInBounds()) {
    auto *Add = dyn_cast<SCEVAddExpr>(PointerSCEV);
    const SCEV *PointerBase = SE.getPointerBase(PointerSCEV);
    const SCEVAddRecExpr *CastedAR = nullptr;
    if (Add && !isa<SCEVCouldNotCompute>(PointerBase)) {
      for (const SCEV *Operand : Add->operands()) {
        if (Operand == PointerBase)
          continue;
        auto *Extend = dyn_cast<SCEVZeroExtendExpr>(Operand);
        auto *Candidate =
            Extend ? dyn_cast<SCEVAddRecExpr>(Extend->getOperand()) : nullptr;
        if (!Candidate || CastedAR)
          return false;
        CastedAR = Candidate;
      }
    }
    auto *InductionAR =
        dyn_cast<SCEVAddRecExpr>(SE.getSCEV(const_cast<PHINode *>(Induction)));
    auto *CastedStart =
        CastedAR ? dyn_cast<SCEVConstant>(CastedAR->getStart()) : nullptr;
    auto *CastedStep =
        CastedAR ? dyn_cast<SCEVConstant>(CastedAR->getStepRecurrence(SE))
                 : nullptr;
    if (!CastedAR || CastedAR != InductionAR || !CastedStart ||
        !CastedStart->getAPInt().isZero() || !CastedStep ||
        !CastedStep->getAPInt().isOne())
      return false;
    AR = CastedAR;
    Start = PointerBase;
  }

  if (!AR || !Start || AR->getLoop() != &L || !AR->isAffine() ||
      (!AR->hasNoSelfWrap() && !(GEP && GEP->isInBounds())))
    return false;

  auto *Step = dyn_cast<SCEVConstant>(AR->getStepRecurrence(SE));
  if (!Step || !Step->getAPInt().isStrictlyPositive() ||
      Step->getAPInt().getActiveBits() > 64)
    return false;

  const SCEVUnknown *BaseSCEV = dyn_cast<SCEVUnknown>(SE.getPointerBase(Start));
  if (!BaseSCEV)
    return false;

  const Value *Base = BaseSCEV->getValue();
  if (!Base->getType()->isPointerTy() || !L.isLoopInvariant(Base))
    return false;

  const SCEV *OffsetSCEV = SE.removePointerBase(Start);
  if (isa<SCEVCouldNotCompute>(OffsetSCEV) ||
      !isSupportedInvariantSCEV(OffsetSCEV, L, SE))
    return false;

  uint64_t Offset = 0;
  bool HasConstantOffset = false;
  if (auto *Constant = dyn_cast<SCEVConstant>(OffsetSCEV)) {
    const APInt &Value = Constant->getAPInt();
    if (!Value.isNegative() && Value.getActiveBits() <= 64) {
      Offset = Value.getZExtValue();
      HasConstantOffset = true;
    }
  }

  Access.start = Start;
  Access.base = Base;
  Access.offset = Offset;
  Access.stride = Step->getAPInt().getZExtValue();
  Access.hasConstantOffset = HasConstantOffset;
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
  return Write.start == Read.start && Write.stride == Read.stride;
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
                                   const SCEV *IterationCount) {
  auto *Count = dyn_cast<SCEVConstant>(IterationCount);
  if (!A.hasConstantOffset || !B.hasConstantOffset)
    return false;
  if (!Count || Count->getAPInt().getActiveBits() > 64)
    return false;

  uint64_t Iterations = Count->getAPInt().getZExtValue();
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

bool addSignedOffset(uint64_t Offset, int64_t Delta, uint64_t &Result) {
  if (Delta >= 0) {
    uint64_t Positive = static_cast<uint64_t>(Delta);
    if (Offset > std::numeric_limits<uint64_t>::max() - Positive)
      return false;
    Result = Offset + Positive;
    return true;
  }

  uint64_t Magnitude = static_cast<uint64_t>(-(Delta + 1)) + 1;
  if (Offset < Magnitude)
    return false;
  Result = Offset - Magnitude;
  return true;
}

bool normalizeRelatedBases(const AffineLoopAccess &A, const AffineLoopAccess &B,
                           const DataLayout &DL, AffineLoopAccess &NormalizedA,
                           AffineLoopAccess &NormalizedB) {
  if (!A.hasConstantOffset || !B.hasConstantOffset)
    return false;

  int64_t BaseOffsetA = 0;
  int64_t BaseOffsetB = 0;
  const Value *BaseA =
      GetPointerBaseWithConstantOffset(A.base, BaseOffsetA, DL, false);
  const Value *BaseB =
      GetPointerBaseWithConstantOffset(B.base, BaseOffsetB, DL, false);
  if (BaseA != BaseB)
    return false;

  uint64_t OffsetA = 0;
  uint64_t OffsetB = 0;
  if (!addSignedOffset(A.offset, BaseOffsetA, OffsetA) ||
      !addSignedOffset(B.offset, BaseOffsetB, OffsetB))
    return false;

  NormalizedA = A;
  NormalizedB = B;
  NormalizedA.base = BaseA;
  NormalizedA.offset = OffsetA;
  NormalizedB.base = BaseB;
  NormalizedB.offset = OffsetB;
  return true;
}

bool areAffineAccessesDisjoint(const AffineLoopAccess &A,
                               const AffineLoopAccess &B,
                               const SCEV *IterationCount,
                               const DataLayout &DL) {
  AffineLoopAccess NormalizedA = A;
  AffineLoopAccess NormalizedB = B;
  if (A.base != B.base &&
      !normalizeRelatedBases(A, B, DL, NormalizedA, NormalizedB))
    return false;
  if (!NormalizedA.hasConstantOffset || !NormalizedB.hasConstantOffset)
    return false;
  if (finiteAffineImagesAreDisjoint(NormalizedA, NormalizedB, IterationCount))
    return true;
  uint64_t Difference = NormalizedA.offset >= NormalizedB.offset
                            ? NormalizedA.offset - NormalizedB.offset
                            : NormalizedB.offset - NormalizedA.offset;
  return Difference %
             greatestCommonDivisor(NormalizedA.stride, NormalizedB.stride) !=
         0;
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
    if (!getAffineAccess(Load->getPointerOperand(), *Summary.loop, SE,
                         Summary.induction, Read))
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
          !areAffineAccessesDisjoint(
              Write.access, Read, Summary.iterationCount,
              Summary.loop->getHeader()->getModule()->getDataLayout()))
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

bool analyzeMemoryLoop(Loop &L, ScalarEvolution &SE, AAResults &AA,
                       MemorySSA &MSSA, DominatorTree &DT,
                       FunctionalLoopSummary &Summary) {
  SupportedControlFlow Flow;
  if (L.getParentLoop() || !L.getSubLoops().empty() ||
      !L.isLoopSimplifyForm() || L.getNumBackEdges() != 1 ||
      !L.getExitingBlock() || !L.getLoopPreheader() || !L.getLoopLatch() ||
      !L.getExitBlock() || !hasSupportedControlFlow(L, Flow))
    return false;

  PHINode *InductionCandidate = L.getCanonicalInductionVariable();
  if (!InductionCandidate)
    InductionCandidate = getSimplePositiveInductionCandidate(L);
  if (!InductionCandidate || !hasOnlySimpleHeaderPhis(L, InductionCandidate))
    return false;
  const Value *InductionStart = nullptr;
  const ConstantInt *InductionStep = nullptr;
  PHINode *Induction = getPositiveInduction(L, SE, InductionCandidate,
                                            InductionStart, InductionStep);
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

  const SCEV *IterationCount = nullptr;
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
  if (!getIterationCount(L, L.getExitingBlock(), SE, IterationType,
                         StoresExecuteBeforeExitTest, IterationCount))
    return false;

  Summary.loop = &L;
  Summary.preheader = L.getLoopPreheader();
  Summary.exit = L.getExitBlock();
  Summary.induction = Induction;
  Summary.inductionStart = InductionStart;
  Summary.inductionStep = InductionStep;
  Summary.inductionEscapes = InductionEscapes;
  Summary.iterationType = IterationType;
  Summary.iterationCount = IterationCount;

  const SCEV *FinalInductionSCEV = SE.getAddExpr(
      SE.getSCEV(const_cast<Value *>(InductionStart)),
      SE.getMulExpr(SE.getSCEV(const_cast<ConstantInt *>(InductionStep)),
                    IterationCount));
  for (Instruction &I : *L.getExitBlock()) {
    auto *Phi = dyn_cast<PHINode>(&I);
    if (!Phi)
      break;
    if (Phi->getNumIncomingValues() != 1 ||
        !L.contains(Phi->getIncomingBlock(0)) ||
        SE.getSCEVAtScope(Phi->getIncomingValue(0), L.getParentLoop()) !=
            FinalInductionSCEV)
      return false;
    Summary.finalInductionPhis.push_back(Phi);
  }

  for (const StoreInst *Store : Stores) {
    AffineLoopAccess Write;
    if (!getAffineAccess(Store->getPointerOperand(), L, SE, Summary.induction,
                         Write))
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
          !areAffineAccessesDisjoint(
              A, B, Summary.iterationCount,
              Summary.loop->getHeader()->getModule()->getDataLayout()) &&
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

bool getInsideAndOutsideSuccessors(Loop &L, BranchInst &Branch,
                                   BasicBlock *&Inside, BasicBlock *&Outside,
                                   bool &InsideOnTrue) {
  if (!Branch.isConditional())
    return false;
  Inside = nullptr;
  Outside = nullptr;
  for (unsigned I = 0; I < 2; ++I) {
    BasicBlock *Successor = Branch.getSuccessor(I);
    if (L.contains(Successor)) {
      if (Inside)
        return false;
      Inside = Successor;
      InsideOnTrue = I == 0;
    } else {
      if (Outside)
        return false;
      Outside = Successor;
    }
  }
  return Inside && Outside;
}

void collectInstructionSlice(const Value *V, Loop &L,
                             std::set<const Instruction *> &Slice) {
  auto *I = dyn_cast<Instruction>(V);
  if (!I || !L.contains(I) || !Slice.insert(I).second)
    return;
  for (const Value *Operand : I->operand_values())
    collectInstructionSlice(Operand, L, Slice);
}

bool hasEscapingLoopValue(Loop &L) {
  for (BasicBlock *BB : L.blocks())
    for (Instruction &I : *BB)
      if (!I.getType()->isVoidTy())
        for (User *U : I.users())
          if (auto *Use = dyn_cast<Instruction>(U))
            if (!L.contains(Use))
              return true;
  return false;
}

bool analyzeReadOnlyPredicateLoop(Loop &L, ScalarEvolution &SE, AAResults &AA,
                                  MemorySSA &MSSA, DominatorTree &DT,
                                  FunctionalLoopSummary &Summary) {
  if (L.getParentLoop() || !L.getSubLoops().empty() ||
      !L.isLoopSimplifyForm() || L.getNumBackEdges() != 1 ||
      !L.getLoopPreheader() || !L.getLoopLatch() || hasEscapingLoopValue(L))
    return false;

  SmallVector<BasicBlock *, 2> ExitingBlocks;
  L.getExitingBlocks(ExitingBlocks);
  if (ExitingBlocks.size() != 2 ||
      llvm::find(ExitingBlocks, L.getHeader()) == ExitingBlocks.end())
    return false;

  BasicBlock *PredicateBlock =
      ExitingBlocks[0] == L.getHeader() ? ExitingBlocks[1] : ExitingBlocks[0];
  auto *BoundBranch = dyn_cast<BranchInst>(L.getHeader()->getTerminator());
  auto *PredicateBranch = dyn_cast<BranchInst>(PredicateBlock->getTerminator());
  BasicBlock *BodyEntry = nullptr;
  BasicBlock *NormalExit = nullptr;
  bool BodyOnTrue = false;
  BasicBlock *ContinueBlock = nullptr;
  BasicBlock *FailureExit = nullptr;
  bool ContinueOnTrue = false;
  if (!BoundBranch || !PredicateBranch ||
      !getInsideAndOutsideSuccessors(L, *BoundBranch, BodyEntry, NormalExit,
                                     BodyOnTrue) ||
      !getInsideAndOutsideSuccessors(L, *PredicateBranch, ContinueBlock,
                                     FailureExit, ContinueOnTrue) ||
      NormalExit == FailureExit || !DT.dominates(BodyEntry, PredicateBlock) ||
      !DT.dominates(PredicateBlock, L.getLoopLatch()))
    return false;

  // Keep exit blocks in the generated program so their return/PHI behavior is
  // preserved.  Direct exit PHIs cannot be populated from the summarized
  // preheader edge, so reject them for this first form.
  if (isa<PHINode>(&NormalExit->front()) || isa<PHINode>(&FailureExit->front()))
    return false;

  PHINode *InductionCandidate = L.getCanonicalInductionVariable();
  if (!InductionCandidate)
    InductionCandidate = getSimplePositiveInductionCandidate(L);
  if (!InductionCandidate || !hasOnlySimpleHeaderPhis(L, InductionCandidate))
    return false;
  for (Instruction &I : *L.getHeader())
    if (auto *Phi = dyn_cast<PHINode>(&I)) {
      if (Phi != InductionCandidate)
        return false;
    } else {
      break;
    }

  const Value *InductionStart = nullptr;
  const ConstantInt *InductionStep = nullptr;
  PHINode *Induction = getPositiveInduction(L, SE, InductionCandidate,
                                            InductionStart, InductionStep);
  auto *IterationType =
      Induction ? dyn_cast<IntegerType>(Induction->getType()) : nullptr;
  if (!IterationType)
    return false;

  const SCEV *IterationCount = nullptr;
  if (!getIterationCount(L, L.getHeader(), SE, IterationType, false,
                         IterationCount))
    return false;

  Summary.kind = FunctionalLoopSummary::Kind::ReadOnlyPredicate;
  Summary.loop = &L;
  Summary.preheader = L.getLoopPreheader();
  Summary.induction = Induction;
  Summary.inductionStart = InductionStart;
  Summary.inductionStep = InductionStep;
  Summary.iterationType = IterationType;
  Summary.iterationCount = IterationCount;
  Summary.predicateBranch = PredicateBranch;
  Summary.normalExit = NormalExit;
  Summary.failureExit = FailureExit;
  Summary.continueConditionValue = ContinueOnTrue;

  if (!validateRhs(PredicateBranch->getCondition(), Summary, SE, AA, MSSA, DT))
    return false;

  std::set<const Instruction *> Required;
  collectInstructionSlice(BoundBranch->getCondition(), L, Required);
  collectInstructionSlice(PredicateBranch->getCondition(), L, Required);
  Required.insert(Induction);
  BasicBlock *Incoming = nullptr;
  BasicBlock *Backedge = nullptr;
  if (!L.getIncomingAndBackEdge(Incoming, Backedge))
    return false;
  auto *InductionUpdate =
      dyn_cast<Instruction>(Induction->getIncomingValueForBlock(Backedge));
  if (!InductionUpdate)
    return false;
  Required.insert(InductionUpdate);

  unsigned LoadCount = 0;
  for (BasicBlock *BB : L.blocks()) {
    auto *Branch = dyn_cast<BranchInst>(BB->getTerminator());
    if (!Branch ||
        (Branch->isConditional() && Branch != BoundBranch &&
         Branch != PredicateBranch) ||
        (Branch->isUnconditional() && !L.contains(Branch->getSuccessor(0))))
      return false;
    for (Instruction &I : *BB) {
      if (isa<DbgInfoIntrinsic>(I) || isa<BranchInst>(I))
        continue;
      if (auto *Load = dyn_cast<LoadInst>(&I)) {
        if (!Load->isSimple())
          return false;
        ++LoadCount;
      } else if (!isa<PHINode>(I) && !isa<BinaryOperator>(I) &&
                 !isa<CastInst>(I) && !isa<GetElementPtrInst>(I) &&
                 !isa<ICmpInst>(I) && !isa<SelectInst>(I)) {
        return false;
      }
      if (!Required.count(&I))
        return false;
    }
  }
  return LoadCount != 0 && LoadCount == Summary.loads.size();
}

} // namespace

std::vector<FunctionalLoopSummary>
FunctionalLoopSummaryAnalysis::analyze(Function &F, LoopInfo &LI,
                                       ScalarEvolution &SE, AAResults &AA,
                                       MemorySSA &MSSA) {
  std::vector<FunctionalLoopSummary> Result;
  DominatorTree DT(F);
  for (Loop *L : LI.getLoopsInPreorder()) {
    FunctionalLoopSummary MemorySummary;
    if (analyzeMemoryLoop(*L, SE, AA, MSSA, DT, MemorySummary)) {
      Result.push_back(std::move(MemorySummary));
      continue;
    }
    FunctionalLoopSummary ReadSummary;
    if (analyzeReadOnlyPredicateLoop(*L, SE, AA, MSSA, DT, ReadSummary))
      Result.push_back(std::move(ReadSummary));
  }
  return Result;
}

} // namespace smack
