//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SIGNANALYSIS_H
#define SIGNANALYSIS_H

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include <map>

namespace smack {

/// Inferred sign for an integer SSA value.
///
/// Lattice:
///        Unknown
///        /     \;
///    Signed   Unsigned
///        \     /
///        Conflict
///
/// Unknown: no consumer supplied window information (and none could forward
///   the value somewhere unseen). Conflict: the value has both signed and
///   unsigned consumers, or it escapes the analysis (stored to memory,
///   passed to a call that cannot be followed, consumed by an opcode the
///   analysis does not model). Both render a negative literal signed, i.e.
///   exactly as SMACK did before this analysis; only Unsigned changes the
///   spelling to the non-negative representative 2^N - k.
enum class Sign { Unknown, Signed, Unsigned, Conflict };

/// Meet operator on the sign lattice.  Unknown is top, Conflict is bottom.
inline Sign meetSign(Sign a, Sign b) {
  if (a == b)
    return a;
  if (a == Sign::Unknown)
    return b;
  if (b == Sign::Unknown)
    return a;
  return Sign::Conflict;
}

/// A demand-driven sign oracle for integer literal uses.
///
/// LLVM integer values are signless, and signedness is not an invariant of an
/// SSA value: the same value can legitimately be consumed by both signed and
/// unsigned operations. This analysis therefore starts at an exact Use and
/// follows only the use-context needed to classify that operand. Results for
/// completed value queries are memoized, so repeated literal uses can share
/// their resolved context without requiring a whole-module scan.
class SignAnalysis : public llvm::ModulePass {
public:
  static char ID;
  SignAnalysis() : llvm::ModulePass(ID) {}
  llvm::StringRef getPassName() const override;
  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  bool runOnModule(llvm::Module &M) override;

  /// Meet the contexts in which V is consumed. This is primarily exposed for
  /// debugging; literal rendering should query an exact Use instead.
  Sign getSign(const llvm::Value *V) const;

  /// Query the inferred sign for a particular operand use.
  ///
  /// Constants have no sign of their own: LLVM uniques them per context, so
  /// one -1 : i32 object is shared by every use in the module. This query
  /// derives sign from the exact operand position and follows transparent SSA
  /// and direct call/return edges only when local evidence is insufficient.
  Sign getSign(const llvm::Use &U) const;

  /// Dump the analysis results to errs() (for debugging).
  void dump() const;

private:
  mutable std::map<const llvm::Value *, Sign> SignCache;

  Sign
  inferValue(const llvm::Value *V,
             llvm::SmallPtrSetImpl<const llvm::Value *> &VisitedValues) const;
  Sign
  inferUse(const llvm::Use &U,
           llvm::SmallPtrSetImpl<const llvm::Value *> &VisitedValues) const;
  Sign legacyLiteralFallback(const llvm::Use &U) const;
};

} // namespace smack

#endif // SIGNANALYSIS_H
