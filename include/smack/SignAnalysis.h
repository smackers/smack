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

/// SMACK's original operation-local sign table for a negative integer literal
/// operand. This is the complete rendering rule when --sign-analysis is off
/// (its output must stay byte-identical to that of earlier releases) and the
/// residue the analysis falls back to for sign-polymorphic bitwise operations
/// on which no consumer supplied a window. Returns Unknown for anything that
/// is not a negative literal of width > 1.
Sign legacyLiteralSign(const llvm::Use &U);

/// A demand-driven sign oracle for integer literal uses.
///
/// LLVM integer values are signless, and signedness is not an invariant of an
/// SSA value: the same value can legitimately be consumed by both signed and
/// unsigned operations. This analysis therefore starts at an exact Use and
/// follows only the use-context needed to classify that operand. Results for
/// completed value queries are memoized, so repeated literal uses can share
/// their resolved context without requiring a whole-module scan.
///
/// Rendering policy (see SmackRep::lit). Under the unbounded integer encoding
/// an N-bit pattern with the top bit set has two representatives, -k and
/// 2^N - k, and every literal that meets a given SSA value must be spelled in
/// the window of that value or equalities silently fail. The invariant this
/// analysis maintains is therefore: a literal is printed in the window given
/// by the inferred sign of the value it meets, and when that sign is not
/// decided nothing is guessed that could break an equality.
///   - Unsigned: the literal is spelled 2^N - k.
///   - Signed:   the literal is spelled -k.
///   - Unknown / Conflict: the literal is spelled -k, exactly as SMACK did
///     before this analysis existed; an eq/ne against such a literal is
///     additionally compared with both representatives
///     (SmackRep::twoWindowEquality), which is exact under this model.
///   - Negative operands of add/sub/mul are always spelled -k: the operations
///     do not wrap under the integer encoding, so that is the only spelling
///     that computes the C decrement.
///
/// Non-locality. The window of a value is the meet over all of its consumers,
/// and the Ret rule meets over every direct call site of the function in the
/// module, so the spelling of a literal inside a phi/select/argument/return
/// is a whole-module property by design: a new caller elsewhere can change
/// it. Any consumer the analysis cannot see through (memory, calls it cannot
/// follow, unmodelled opcodes) makes the value Conflict, so only a value whose
/// entire consumer set is classified takes the unsigned window.
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
};

} // namespace smack

#endif // SIGNANALYSIS_H
