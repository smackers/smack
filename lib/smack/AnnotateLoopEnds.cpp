//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass normalizes loop structures to allow easier generation of Boogie
// code when a loop edge comes from a branch. Specifically, a forwarding block
// is added between a branching block and the loop header.
//

#include "smack/AnnotateLoopEnds.h"
#include "smack/Naming.h"
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
void AnnotateLoopEnds::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequiredID(LoopSimplifyID);
  AU.addRequired<LoopInfoWrapperPass>();
}

void insertLoopEndAssertion(Function *le, Instruction *insertBefore) {
  CallInst::Create(le, "", insertBefore);
}

void processExitBlock(BasicBlock *block, Function *le) {
  // print exit block found!!

  errs() << "    Exit block found! \n";

  Instruction& front = block->front();
  insertLoopEndAssertion(le,&front);
}

void annotateLoopEnd(Loop *loop, Function *le) {
  //BasicBlock *headerBlock = loop->getHeader();

  // I imagine that it is very uncommon for a loop to have
  //   more than 5 exit points.
  SmallVector<BasicBlock *, 5> exitBlocks; 

  loop->getExitBlocks(exitBlocks);
  
  for (BasicBlock *b : exitBlocks) {
    processExitBlock(b,le);
  } 

  // Handle subloops
  //for (Loop *subloop : loop->getSubLoops()) {
  //  processLoop(subloop);
  //}
}

bool AnnotateLoopEnds::runOnModule(Module &m) {

  Function *le = m.getFunction("__SMACK_loop_end");
  assert(le != NULL && "Function __SMACK_loop_end shoudl be present.");

  errs() << "Module Start\n";
  for (auto F = m.begin(), FEnd = m.end(); F != FEnd; ++F) {
    if (F->isIntrinsic() || F->empty()) {
      continue;
    }

    errs() << "Hello " << F->getName() << "\n";

    LoopInfo &loopInfo = getAnalysis<LoopInfoWrapperPass>(*F).getLoopInfo();
    for (LoopInfo::iterator LI = loopInfo.begin(), LIEnd = loopInfo.end();
         LI != LIEnd; ++LI) {

      errs() << "  Loop Found in " << F->getName() << "\n";
      annotateLoopEnd(*LI, le);
    }
  }

  return true;
}

// Pass ID variable
char AnnotateLoopEnds::ID = 0;

StringRef AnnotateLoopEnds::getPassName() const { return "Annotate Loop Ends with assert(false)"; }
} // namespace smack
