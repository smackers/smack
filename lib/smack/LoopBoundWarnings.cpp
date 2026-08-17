//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "smack-loop-bound-warnings"
#include "smack/LoopBoundWarnings.h"
#include "smack/Debug.h"
#include "smack/SmackOptions.h"
#include "smack/SmackWarnings.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include <string>

namespace smack {

using namespace llvm;

void LoopBoundWarnings::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<ScalarEvolutionWrapperPass>();
  // Deliberately *not* `AU.addRequiredID(LoopSimplifyID)`, unlike the sibling
  // AnnotateLoopExits pass. LoopSimplify is a transformation: it adds
  // preheaders and dedicated exit blocks, which changes the module that
  // sea-dsa, smack::Regions and SmackModuleGenerator later see. All it buys
  // this pass is trip counts for loops with several backedges, a shape clang
  // does not emit at -O0, and it is not worth perturbing the translation of
  // every program to recover.
}

namespace {

// Renders the loop's source range for the warning message.
//
// LLVM keeps a loop's source range in its `llvm.loop` metadata, but that
// metadata is often simply not there: bitcode handed to SMACK directly (the
// `.bc`/`.ll` frontend passes it through untouched, see
// share/smack/frontend.py) may carry no debug info at all, and any transform
// that rewrites the latch drops it. `Loop::getLocRange` then falls back to the
// header terminator's debug location, and when that is missing too it returns
// a range of two *null* DebugLocs. Calling `getLine()` on one of those is a
// straight null dereference rather than a failed assertion, because the LLVM
// most distributions ship is built with assertions off -- hence the guards.
std::string describeLoopSource(const Loop *loop) {
  auto range = loop->getLocRange();
  auto start = range.getStart();
  auto end = range.getEnd();

  if (!start)
    return "";

  std::string description;
  raw_string_ostream os(description);
  if (end && end.getLine() != start.getLine())
    os << " from line " << start.getLine() << " to line " << end.getLine();
  else
    os << " at line " << start.getLine();
  return os.str();
}

void warnAboutLoop(const Function &F, const Loop *loop, ScalarEvolution &SE) {
  // ScalarEvolution offers several notions of "how long does this loop run",
  // and the trip count is the one that answers the user's actual question,
  // because it is exactly the smallest `--unroll` value that covers the loop.
  // The regression pairs in test/c/unroll pin this down: `for (a = 0; a < 10;
  // a++)` verifies vacuously at `--unroll=10` and reports its bug at
  // `--unroll=11`, and 11 is precisely the trip count LLVM computes for it.
  //
  // The obvious-looking alternative, `getConstantMaxBackedgeTakenCount`, is
  // unusable here. It is documented as a conservative over-approximation, so
  // when the count is symbolic it falls back on the range of the counter's
  // type: for the extremely common `for (i = 0; i < n; i++)` over an `int` it
  // returns 2147483647, and reporting that as a "known loop bound" is worse
  // than reporting nothing. `getSmallConstantTripCount` yields 0 unless the
  // count really is a small constant, which is the distinction we want.
  //
  // One caveat worth knowing: a trip count counts executions of the loop
  // header, so it is one more than the number of iterations for the top-tested
  // loops clang emits at -O0, but equal to it for the bottom-tested loops
  // LoopRotate produces under `--static-unroll`. That difference does not
  // matter in practice, because `--static-unroll` runs LoopUnroll and any loop
  // whose trip count is a known constant is gone by the time we get here.
  unsigned tripCount = SE.getSmallConstantTripCount(loop);
  unsigned unrollBound = SmackOptions::UnrollBound;

  // The bound already covers every execution of this loop, so nothing is
  // missed and there is nothing worth saying.
  if (tripCount != 0 && unrollBound != 0 && tripCount <= unrollBound)
    return;

  std::string description;
  raw_string_ostream os(description);
  os << "found loop" << describeLoopSource(loop) << " in function "
     << F.getName() << ": ";

  if (tripCount != 0)
    os << "--unroll=" << tripCount << " is needed to explore it fully";
  else
    os << "its bound cannot be determined statically";

  // Zero means the driver did not tell us the bound: either llvm2bpl was run
  // on its own, or `--modular` is in effect and loops are not unrolled to a
  // fixed depth at all.
  if (unrollBound != 0)
    os << " (current bound is " << unrollBound << ")";

  // Passing the header's terminator gives the message the usual
  // `file:line:col:` prefix, which is what distinguishes a loop in the user's
  // code from one in SMACK's own bundled C library.
  SmackWarnings::warnLoop(os.str(), loop->getHeader()->getTerminator());
}

} // namespace

bool LoopBoundWarnings::runOnFunction(Function &F) {
  auto &loopInfo = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();

  // `getLoopsInPreorder`, not `begin()`/`end()`: the latter walks only the
  // outermost loops, and in a nest it is normally the inner loop that needs
  // the larger bound.
  for (auto *loop : loopInfo.getLoopsInPreorder())
    warnAboutLoop(F, loop, SE);

  return false;
}

char LoopBoundWarnings::ID = 0;

StringRef LoopBoundWarnings::getPassName() const {
  return "Warn about loops whose unroll bound may be insufficient";
}
} // namespace smack
