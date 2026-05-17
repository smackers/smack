//
// This file is distributed under the MIT License. See LICENSE for details.
//
// Give integer allocas with a load not dominated by any store one named
// nondet initializer. This keeps mem2reg from turning one C local into
// several unrelated LLVM undef values, while skipping escaping allocas
// that SMACK's memory lowering must handle.
//

#include "smack/InitUndefAllocas.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace smack {

char InitUndefAllocas::ID = 0;

void InitUndefAllocas::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
}

namespace detail {

bool runInitUndefAllocas(Function &F, DominatorTree &DT) {
  Module *M = F.getParent();
  bool changed = false;

  // Collect candidate allocas first; mutating the IR while iterating
  // would invalidate iterators.
  SmallVector<AllocaInst *, 16> candidates;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *AI = dyn_cast<AllocaInst>(&I)) {
        if (AI->getAllocatedType()->isIntegerTy()) {
          candidates.push_back(AI);
        }
      }
    }
  }

  for (AllocaInst *AI : candidates) {
    SmallVector<StoreInst *, 4> stores;
    SmallVector<LoadInst *, 8> loads;
    bool escapes = false;

    for (User *U : AI->users()) {
      if (auto *SI = dyn_cast<StoreInst>(U)) {
        // Only count stores TO this alloca, not stores OF its pointer.
        if (SI->getPointerOperand() == AI) {
          stores.push_back(SI);
        } else {
          escapes = true;
          break;
        }
      } else if (auto *LI = dyn_cast<LoadInst>(U)) {
        loads.push_back(LI);
      } else {
        escapes = true;
        break;
      }
    }

    if (escapes) continue;
    if (loads.empty()) continue;  // dead alloca, nothing reads it

    // Initialized iff every load is dominated by SOME store.
    bool allLoadsDominated = true;
    for (LoadInst *LI : loads) {
      bool dominated = false;
      for (StoreInst *SI : stores) {
        if (DT.dominates(SI, LI)) {
          dominated = true;
          break;
        }
      }
      if (!dominated) {
        allLoadsDominated = false;
        break;
      }
    }
    if (allLoadsDominated) continue;

    // Genuinely uninitialized along at least one load path. Insert
    // ``store i<N> __SMACK_nondet_<type>(), <alloca>`` immediately
    // after the alloca so mem2reg propagates a single named call
    // result to every disconnected use.
    Type *allocTy = AI->getAllocatedType();
    unsigned bits = allocTy->getIntegerBitWidth();
    std::string fnName = (bits <= 32) ? "__SMACK_nondet_int"
                                      : "__SMACK_nondet_long";
    FunctionType *fnTy = FunctionType::get(allocTy, false);
    FunctionCallee nondetFn = M->getOrInsertFunction(fnName, fnTy);

    IRBuilder<> builder(AI->getNextNode());
    Value *nondetVal = builder.CreateCall(nondetFn);
    builder.CreateStore(nondetVal, AI);
    changed = true;
  }

  return changed;
}

} // namespace detail

bool InitUndefAllocas::runOnFunction(Function &F) {
  DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  return detail::runInitUndefAllocas(F, DT);
}

llvm::PreservedAnalyses
InitUndefAllocasNewPM::run(Function &F, llvm::FunctionAnalysisManager &FAM) {
  DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);
  bool changed = detail::runInitUndefAllocas(F, DT);
  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

} // namespace smack
