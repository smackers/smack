//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "simplify-libcalls"

#include "smack/SimplifyLibCalls.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <map>
#include <set>
#include <stack>
#include <vector>

namespace smack {

using namespace llvm;

void SimplifyLibCalls::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<TargetLibraryInfoWrapperPass>();
}

bool SimplifyLibCalls::runOnFunction(Function &F) {
  modified = false;
  simplifier = new LibCallSimplifier(
      F.getParent()->getDataLayout(),
      &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F),
      getAnalysis<OptimizationRemarkEmitterWrapperPass>().getORE(),
      &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI(),
      &getAnalysis<ProfileSummaryInfoWrapperPass>().getPSI());
  if (simplifier)
    visit(F);
  return modified;
}

void SimplifyLibCalls::visitCallInst(CallInst &I) {
  if (I.getCalledFunction()) {
    IRBuilder<> B(I.getContext());
    if (simplifier->optimizeCall(&I, B))
      I.eraseFromParent();
  }
}

// Pass ID variable
char SimplifyLibCalls::ID = 0;

// Register the pass
static RegisterPass<SimplifyLibCalls> X("simplify-libcalls",
                                        "Simplify Library Calls");
} // namespace smack
