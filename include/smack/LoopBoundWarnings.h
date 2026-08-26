//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_LOOP_BOUND_WARNINGS_H
#define SMACK_LOOP_BOUND_WARNINGS_H

#include "llvm/Pass.h"
#include <set>
#include <vector>

namespace llvm {
class Function;
class Loop;
class LoopInfo;
class ScalarEvolution;
} // namespace llvm

namespace smack {

struct LoopBoundInfo {
  const llvm::Loop *loop;
  unsigned tripCount;
};

// Retrieve trip counts recorded by LoopBoundWarnings before NormalizeLoops.
// Functional loop lowering emits warnings later, after it knows which loops
// were summarized, without querying ScalarEvolution on normalized loops.
std::vector<LoopBoundInfo> recordedLoopBoundInfo(llvm::LoopInfo &LI);

void warnAboutLoops(const llvm::Function &F,
                    const std::vector<LoopBoundInfo> &LoopBounds,
                    const std::set<const llvm::Loop *> &IgnoredLoops = {});

// Emit the usual bound warning for every loop except those in IgnoredLoops.
// Functional loop lowering calls this only after its final memory-model
// eligibility checks, so a rejected loop never loses its warning.
void warnAboutLoops(const llvm::Function &F, llvm::LoopInfo &LI,
                    llvm::ScalarEvolution &SE,
                    const std::set<const llvm::Loop *> &IgnoredLoops = {});

// SMACK is a *bounded* verifier: whichever back end runs, every loop is
// explored at most `--unroll N` times (Boogie's `/loopUnroll:N`, Corral's
// `/recursionBound:N`). A bug that first shows up on iteration N+1 is
// therefore invisible, and SMACK reports "no errors" -- a false negative that
// is indistinguishable, from the outside, from a real proof.
//
// This pass exists to make that gap visible. For each loop it asks LLVM's
// ScalarEvolution for a constant trip count and then reports one of:
//
//   * trip count known and <= the unroll bound: nothing. The bound already
//     covers every execution of the loop, so there is nothing to warn about.
//   * trip count known and > the unroll bound: the exact `--unroll` value that
//     would cover the loop, so the user can simply raise the flag.
//   * trip count not statically computable: a note that the loop is explored
//     only up to the unroll bound.
//
// Normally the pass only emits diagnostics and returns false. With
// --functionalize-loops it records the computed counts as instruction
// metadata before NormalizeLoops and returns true; all semantic analyses are
// still preserved. Boogie generation emits the deferred warnings once the
// exact set of loops replaced by summaries is known.
//
// This partially addresses issue #760, which asked for CBMC-style automatic
// loop-bound computation. The complementary existing feature is
// `--fail-on-loop-exit` (smack::AnnotateLoopExits): where this pass answers
// "what bound does this loop need?" statically and up front, that one answers
// "was the bound I chose actually enough?" by asserting false at each loop
// exit and letting the back end tell you whether the exit was reachable.
class LoopBoundWarnings : public llvm::FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  LoopBoundWarnings() : llvm::FunctionPass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnFunction(llvm::Function &F) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage &) const override;
};
} // namespace smack

#endif // SMACK_LOOP_BOUND_WARNINGS_H
