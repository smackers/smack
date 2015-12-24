//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "simplify-libcalls"

#include "smack/SmackOptions.h"
#include "smack/Naming.h"
#include "smack/SimplifyLibCalls.h"
#include "llvm/Support/Debug.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <vector>
#include <stack>
#include <map>
#include <set>

namespace smack {

using namespace llvm;

void SimplifyLibCalls::getAnalysisUsage(AnalysisUsage& AU) const {
  AU.setPreservesAll();
  AU.addRequired<DataLayoutPass>();
  AU.addRequired<TargetLibraryInfo>();
}

bool SimplifyLibCalls::runOnModule(Module& M) {
  modified = false;
  simplifier = new LibCallSimplifier(
    &getAnalysis<DataLayoutPass>().getDataLayout(),
    &getAnalysis<TargetLibraryInfo>(),
    false
  );
  if (simplifier)
    visit(M);
  return modified;
}

void SimplifyLibCalls::visitCallInst(CallInst &I) {
  if (I.getCalledFunction())
    if (simplifier->optimizeCall(&I))
      I.eraseFromParent();
}

// Pass ID variable
char SimplifyLibCalls::ID = 0;

// Register the pass
static RegisterPass<SimplifyLibCalls>
X("simplify-libcalls", "Simplify Library Calls");

}
