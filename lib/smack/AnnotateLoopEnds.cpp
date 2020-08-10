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
  AU.addRequired<LoopInfoWrapperPass>();
}

void processExitingBlock(BasicBlock *block) {
  // print exit block found!!

  errs() << "    Exit block found! \n";

}

void annotateLoopEnd(Loop *loop) {
  //BasicBlock *headerBlock = loop->getHeader();

  // I imagine that it is very uncommon for a loop to have
  //   more than 5 exit points.
  SmallVector<BasicBlock *, 5> exitingBlocks; 

  loop->getExitingBlocks(exitingBlocks);
  
  for (BasicBlock *b : exitingBlocks) {
    processExitingBlock(b);
  } 

  // Handle subloops
  //for (Loop *subloop : loop->getSubLoops()) {
  //  processLoop(subloop);
  //}
}

bool AnnotateLoopEnds::runOnFunction(Function &F) {
  if (F.isIntrinsic() || F.empty()) {
    return false;
  }
  errs() << "Hello " << F.getName() << "\n";
  LoopInfo &loopInfo = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  for (LoopInfo::iterator LI = loopInfo.begin(), LIEnd = loopInfo.end();
       LI != LIEnd; ++LI) {
    errs() << "  Loop Found in " << F.getName() << "\n";
    annotateLoopEnd(*LI);
  }

  return true;
}

// Pass ID variable
char AnnotateLoopEnds::ID = 0;

StringRef AnnotateLoopEnds::getPassName() const { return "Annotate Loop Ends with assert(false)"; }
} // namespace smack
