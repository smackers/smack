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
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"

namespace smack {

using namespace llvm;

namespace {

bool getIterationCount(Loop &L, ScalarEvolution &SE, IntegerType *Ty,
                       const Value *&Count) {
  const SCEV *S = SE.getExitCount(&L, L.getHeader());
  if (isa<SCEVCouldNotCompute>(S) || S->getType() != Ty)
    return false;

  if (auto *C = dyn_cast<SCEVConstant>(S))
    Count = C->getValue();
  else if (auto *U = dyn_cast<SCEVUnknown>(S))
    Count = U->getValue();
  else
    return false;

  return Count->getType() == Ty && L.isLoopInvariant(Count);
}

PHINode *getUnitInduction(Loop &L, ScalarEvolution &SE) {
  PHINode *Result = nullptr;
  for (auto &I : *L.getHeader()) {
    auto *Phi = dyn_cast<PHINode>(&I);
    if (!Phi)
      break;

    auto *AR = dyn_cast<SCEVAddRecExpr>(SE.getSCEV(Phi));
    if (!AR || AR->getLoop() != &L || !AR->isAffine())
      return nullptr;
    auto *Start = dyn_cast<SCEVConstant>(AR->getStart());
    auto *Step = dyn_cast<SCEVConstant>(AR->getStepRecurrence(SE));
    if (!Start || !Start->getAPInt().isZero() || !Step ||
        !Step->getAPInt().isOne() || Result)
      return nullptr;
    Result = Phi;
  }
  return Result;
}

bool getAffineAccess(const Value *Pointer, Loop &L, ScalarEvolution &SE,
                     AffineLoopAccess &Access) {
  auto *AR = dyn_cast<SCEVAddRecExpr>(SE.getSCEV(const_cast<Value *>(Pointer)));
  if (!AR || AR->getLoop() != &L || !AR->isAffine() || !AR->hasNoSelfWrap())
    return false;

  auto *Start = dyn_cast<SCEVUnknown>(AR->getStart());
  auto *Step = dyn_cast<SCEVConstant>(AR->getStepRecurrence(SE));
  if (!Start || !Step || !Step->getAPInt().isStrictlyPositive() ||
      Step->getAPInt().getActiveBits() > 64)
    return false;

  const Value *Base = Start->getValue();
  if (!Base->getType()->isPointerTy() || !L.isLoopInvariant(Base))
    return false;

  Access.base = Base;
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

bool validateRhs(const Value *V, FunctionalLoopSummary &Summary,
                 ScalarEvolution &SE, AAResults &AA, MemorySSA &MSSA) {
  if (isa<Constant>(V) || V == Summary.induction)
    return true;

  auto *I = dyn_cast<Instruction>(V);
  if (!I || !Summary.loop->contains(I))
    return Summary.loop->isLoopInvariant(V);

  if (auto *Load = dyn_cast<LoadInst>(I)) {
    if (!Load->isSimple())
      return false;
    if (findLoadAccess(Summary, Load))
      return true;

    AffineLoopAccess Read;
    if (!getAffineAccess(Load->getPointerOperand(), *Summary.loop, SE, Read))
      return false;

    // Before/after locations cover every affine offset within each underlying
    // object, which is the all-iterations proof needed here.  A same-iteration
    // NoAlias query would be insufficient.
    const Value *WriteObject = getUnderlyingObject(Summary.write.base);
    const Value *ReadObject = getUnderlyingObject(Read.base);
    if (!AA.isNoAlias(WriteObject, ReadObject))
      return false;

    auto *MA = MSSA.getMemoryAccess(Load);
    if (!MA)
      return false;
    MemoryAccess *Clobber = MSSA.getWalker()->getClobberingMemoryAccess(MA);
    if (!MSSA.isLiveOnEntryDef(Clobber) &&
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
      return validateRhs(BO->getOperand(0), Summary, SE, AA, MSSA) &&
             validateRhs(BO->getOperand(1), Summary, SE, AA, MSSA);
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
             validateRhs(Cast->getOperand(0), Summary, SE, AA, MSSA);
    default:
      return false;
    }
  }

  return false;
}

bool hasSupportedControlFlow(Loop &L) {
  auto *HeaderBranch = dyn_cast<BranchInst>(L.getHeader()->getTerminator());
  if (!HeaderBranch || !HeaderBranch->isConditional())
    return false;

  for (BasicBlock *BB : L.blocks()) {
    auto *Branch = dyn_cast<BranchInst>(BB->getTerminator());
    if (!Branch)
      return false;
    if (BB == L.getHeader())
      continue;
    if (!Branch->isUnconditional() || !L.contains(Branch->getSuccessor(0)))
      return false;
  }
  return true;
}

bool hasEscapingValue(Loop &L) {
  for (BasicBlock *BB : L.blocks())
    for (Instruction &I : *BB)
      if (!I.getType()->isVoidTy())
        for (User *U : I.users())
          if (auto *Use = dyn_cast<Instruction>(U))
            if (!L.contains(Use))
              return true;
  return false;
}

bool hasOnlySupportedInstructions(Loop &L, const StoreInst *&Store) {
  for (BasicBlock *BB : L.blocks()) {
    for (Instruction &I : *BB) {
      if (isa<DbgInfoIntrinsic>(I))
        continue;
      if (auto *SI = dyn_cast<StoreInst>(&I)) {
        if (Store || !SI->isSimple())
          return false;
        Store = SI;
        continue;
      }
      if (isa<LoadInst>(I) || isa<PHINode>(I) || isa<BinaryOperator>(I) ||
          isa<CastInst>(I) || isa<GetElementPtrInst>(I) || isa<ICmpInst>(I) ||
          isa<BranchInst>(I))
        continue;
      return false;
    }
  }
  return Store != nullptr;
}

bool analyzeLoop(Loop &L, ScalarEvolution &SE, AAResults &AA, MemorySSA &MSSA,
                 FunctionalLoopSummary &Summary) {
  if (L.getParentLoop() || !L.getSubLoops().empty() ||
      !L.isLoopSimplifyForm() || L.getNumBackEdges() != 1 ||
      L.getExitingBlock() != L.getHeader() || !L.getLoopPreheader() ||
      !L.getLoopLatch() || !L.getExitBlock() || !hasSupportedControlFlow(L) ||
      hasEscapingValue(L))
    return false;

  for (Instruction &I : *L.getExitBlock())
    if (isa<PHINode>(I))
      return false;

  PHINode *Induction = getUnitInduction(L, SE);
  auto *IterationType =
      Induction ? dyn_cast<IntegerType>(Induction->getType()) : nullptr;
  if (!IterationType)
    return false;

  const Value *IterationCount = nullptr;
  if (!getIterationCount(L, SE, IterationType, IterationCount))
    return false;

  const StoreInst *Store = nullptr;
  if (!hasOnlySupportedInstructions(L, Store))
    return false;

  Summary.loop = &L;
  Summary.preheader = L.getLoopPreheader();
  Summary.exit = L.getExitBlock();
  Summary.induction = Induction;
  Summary.iterationType = IterationType;
  Summary.iterationCount = IterationCount;
  Summary.store = Store;

  if (!getAffineAccess(Store->getPointerOperand(), L, SE, Summary.write))
    return false;

  return validateRhs(Store->getValueOperand(), Summary, SE, AA, MSSA);
}

} // namespace

std::vector<FunctionalLoopSummary>
FunctionalLoopSummaryAnalysis::analyze(Function &F, LoopInfo &LI,
                                       ScalarEvolution &SE, AAResults &AA,
                                       MemorySSA &MSSA) {
  std::vector<FunctionalLoopSummary> Result;
  for (Loop *L : LI.getLoopsInPreorder()) {
    FunctionalLoopSummary Summary;
    if (analyzeLoop(*L, SE, AA, MSSA, Summary))
      Result.push_back(std::move(Summary));
  }
  return Result;
}

} // namespace smack
