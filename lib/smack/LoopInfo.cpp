//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "smack-loop-info"
#include "smack/LoopInfo.h"
#include "smack/Debug.h"
#include "smack/SmackWarnings.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Support/raw_ostream.h"

namespace smack {

using namespace llvm;

void LoopInfo::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<ScalarEvolutionWrapperPass>();
}

bool LoopInfo::runOnFunction(Function &F) {
  auto &loopInfo = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  for (auto LI = loopInfo.begin(), LIEnd = loopInfo.end(); LI != LIEnd; ++LI) {
    auto L = *LI;
    auto lr = L->getLocRange();
    auto sl = lr.getStart();
    auto el = lr.getEnd();
    std::string description;
    raw_string_ostream o(description);
    o << "found loop from line " << sl.getLine() << " to line " << el.getLine()
      << " in function " << F.getName() << " with ";
    // TODO: figure out why induction variable won't work
    // auto bs = L->getInductionVariable(SE);
    if (auto C =
            dyn_cast<SCEVConstant>(SE.getConstantMaxBackedgeTakenCount(L))) {
      auto CI = C->getValue()->getValue().getZExtValue();
      o << "known loop bound " << CI;
    } else
      o << "unknown loop bound";
    SmackWarnings::warnLoop(o.str());
  }
  return false;
}

char LoopInfo::ID = 0;

StringRef LoopInfo::getPassName() const {
  return "Get Loop Information for the purpose of sound analysis";
}
} // namespace smack
