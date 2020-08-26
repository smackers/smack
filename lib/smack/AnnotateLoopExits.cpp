//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass adds an annotation to the exit of any loop, with the purpose
// of debugging instances where the unroll bound does not unroll enough
// to reach the loop exit. 
//

#define DEBUG_TYPE "smack-loop-unroll"
#include "smack/AnnotateLoopExits.h"
#include "smack/Naming.h"
#include "smack/Debug.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueSymbolTable.h"
#include <map>
#include <set>
#include <vector>

#include "llvm/Support/raw_ostream.h"

namespace smack {

using namespace llvm;

// Register LoopInfo
void AnnotateLoopExits::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequiredID(LoopSimplifyID);
  AU.addRequired<LoopInfoWrapperPass>();
}

// This method is for clarity and self-documentingness
void insertLoopExitAssertion(Function *le, Instruction *insertBefore) {
  CallInst::Create(le, "", insertBefore);
}

void processExitBlock(BasicBlock *block, Function *le) {

  SDEBUG(errs() << "Processing an Exit Block\n");

  Instruction &front = block->front();
  insertLoopExitAssertion(le, &front);
}

void annotateLoopExit(Loop *loop, Function *le) {

  SmallVector<BasicBlock *, 0> exitBlocks;

  loop->getExitBlocks(exitBlocks);

  for (BasicBlock *b : exitBlocks) {
    processExitBlock(b, le);
  }
}

bool AnnotateLoopExits::runOnModule(Module &m) {
  Function *le = m.getFunction(Naming::LOOP_EXIT);
  assert(le != NULL && "Function __SMACK_loop_exit should be present.");

  for (auto F = m.begin(), FEnd = m.end(); F != FEnd; ++F) {
    if (F->isIntrinsic() || F->empty()) {
      continue;
    }

    LoopInfo &loopInfo = getAnalysis<LoopInfoWrapperPass>(*F).getLoopInfo();
    for (LoopInfo::iterator LI = loopInfo.begin(), LIEnd = loopInfo.end();
         LI != LIEnd; ++LI) {

      SDEBUG(errs() << "Processing Loop in " << F->getName() << "\n");
      annotateLoopExit(*LI, le);
    }
  }

  return true;
}

// Pass ID variable
char AnnotateLoopExits::ID = 0;

StringRef AnnotateLoopExits::getPassName() const {
  return "Annotate Loop Exits with assert(false)";
}

} // namespace smack
