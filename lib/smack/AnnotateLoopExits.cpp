//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass normalizes loop structures to allow easier generation of Boogie
// code when a loop edge comes from a branch. Specifically, a forwarding block
// is added between a branching block and the loop header.
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
void insertLoopEndAssertion(Function *le, Instruction *insertBefore) {
  CallInst::Create(le, "", insertBefore);
}

void processExitBlock(BasicBlock *block, Function *le) {
  // print exit block found!!

  SDEBUG(errs() << "Processing an Exit Block\n");

  Instruction& front = block->front();
  insertLoopEndAssertion(le,&front);
}

void annotateLoopEnd(Loop *loop, Function *le) {
  //BasicBlock *headerBlock = loop->getHeader();

  // I imagine that it is very uncommon for a loop to have
  //   more than 5 exit points. This is a complete guess
  //   and we could probably have a better heuristic
  SmallVector<BasicBlock *, 5> exitBlocks; 

  loop->getExitBlocks(exitBlocks);
  
  for (BasicBlock *b : exitBlocks) {
    processExitBlock(b,le);
  } 
}

bool AnnotateLoopExits::runOnModule(Module &m) {

  Function *le = m.getFunction("__SMACK_loop_end");
  assert(le != NULL && "Function __SMACK_loop_end shoudl be present.");

  for (auto F = m.begin(), FEnd = m.end(); F != FEnd; ++F) {
    if (F->isIntrinsic() || F->empty()) {
      continue;
    }

    LoopInfo &loopInfo = getAnalysis<LoopInfoWrapperPass>(*F).getLoopInfo();
    for (LoopInfo::iterator LI = loopInfo.begin(), LIEnd = loopInfo.end();
         LI != LIEnd; ++LI) {

      SDEBUG(errs() << "Processing Loop in " << F->getName() << "\n");
      annotateLoopEnd(*LI, le);
    }
  }

  return true;
}

// Pass ID variable
char AnnotateLoopExits::ID = 0;

StringRef AnnotateLoopExits::getPassName() const { return "Annotate Loop Ends with assert(false)"; }
} // namespace smack
