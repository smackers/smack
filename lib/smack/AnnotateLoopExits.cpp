//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass adds an annotation to the exit of any loop, with the purpose
// of debugging instances where the unroll bound does not unroll enough
// to reach the loop exit.
//

#include "smack/AnnotateLoopExits.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Transforms/Utils.h"
#include <map>
#include <set>
#include <vector>

#include "llvm/Support/raw_ostream.h"

#define DEBUG_TYPE "smack-loop-unroll"

namespace smack {

using namespace llvm;

bool AnnotateLoopExits::doInitialization(Module &M) {
  LoopExitFunction = M.getFunction(Naming::LOOP_EXIT);
  assert(LoopExitFunction != nullptr &&
         "Function __SMACK_loop_exit should be present.");
  return true;
}

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

namespace detail {

bool runAnnotateLoopExits(Function &F, LoopInfo &loopInfo,
                          Function *loopExitFn) {
  if (F.isIntrinsic() || F.empty()) {
    return false;
  }

  for (LoopInfo::iterator LI = loopInfo.begin(), LIEnd = loopInfo.end();
       LI != LIEnd; ++LI) {

    SDEBUG(errs() << "Processing Loop in " << F.getName() << "\n");
    annotateLoopExit(*LI, loopExitFn);
  }

  return true;
}

} // namespace detail

bool AnnotateLoopExits::runOnFunction(Function &F) {
  LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  return detail::runAnnotateLoopExits(F, LI, LoopExitFunction);
}

llvm::PreservedAnalyses
AnnotateLoopExitsNewPM::run(Function &F, llvm::FunctionAnalysisManager &FAM) {
  Module *M = F.getParent();
  Function *loopExitFn = M ? M->getFunction(Naming::LOOP_EXIT) : nullptr;
  assert(loopExitFn != nullptr &&
         "Function __SMACK_loop_exit should be present.");
  LoopInfo &LI = FAM.getResult<llvm::LoopAnalysis>(F);
  bool changed = detail::runAnnotateLoopExits(F, LI, loopExitFn);
  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

// Pass ID variable
char AnnotateLoopExits::ID = 0;

StringRef AnnotateLoopExits::getPassName() const {
  return "Annotate Loop Exits with assert(false)";
}

} // namespace smack
