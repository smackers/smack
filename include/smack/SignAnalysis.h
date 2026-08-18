//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SIGNANALYSIS_H
#define SIGNANALYSIS_H

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include <map>
#include <vector>

namespace seadsa {
class Node;
}

namespace smack {

class DSAWrapper;

/// Inferred sign for an integer SSA value.
///
/// Lattice:
///        Unknown
///        /     \;
///    Signed   Unsigned
///        \     /
///        Conflict
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

/// Module pass that infers the sign (signed / unsigned / unknown / conflict)
/// of every integer-typed SSA value via bidirectional dataflow analysis,
/// including propagation through memory via sea-dsa alias information.
class SignAnalysis : public llvm::ModulePass {
public:
  static char ID;
  SignAnalysis() : llvm::ModulePass(ID) {}
  llvm::StringRef getPassName() const override;
  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  bool runOnModule(llvm::Module &M) override;

  /// Query the inferred sign for a value.  Returns Unknown for values
  /// not in the map, which includes every constant -- see update().
  Sign getSign(const llvm::Value *V) const;

  /// Sign to use when rendering a *constant operand* of \p U.
  ///
  /// Constants have no sign of their own: LLVM uniques them per context, so
  /// one `-1 : i32` object is shared by every use in the module and any sign
  /// recorded for it would leak between unrelated functions.  The sign of a
  /// constant operand is therefore taken from the surrounding computation --
  /// the user's own inferred sign, or failing that the meet of its
  /// non-constant integer operands.  Returns Unknown for a null \p U.
  Sign getConstantOperandSign(const llvm::User *U) const;

  /// Dump the analysis results to errs() (for debugging).
  void dump() const;

private:
  using MemCell = std::pair<const seadsa::Node *, unsigned>;

  std::map<const llvm::Value *, Sign> SignMap;

  /// Index connecting loads and stores through DSA alias cells.
  std::map<MemCell, std::vector<const llvm::Value *>> CellStores;
  std::map<MemCell, std::vector<const llvm::Value *>> CellLoads;

  DSAWrapper *DSA = nullptr;

  /// Meet sign S into V's current mapping.  Returns true if changed.
  bool update(const llvm::Value *V, Sign S);

  /// Resolve a pointer to its abstract memory cell via DSA.
  /// Returns {nullptr, 0} if resolution fails.
  MemCell resolvePointer(const llvm::Value *Ptr);

  /// Build the CellStores/CellLoads indices from all load/store instructions.
  void buildMemoryIndex(llvm::Module &M);

  /// Seed the map from obvious defs and uses.
  void initialize(llvm::Module &M);

  /// One round of forward + backward propagation.  Returns true if
  /// any mapping changed.
  bool propagate(llvm::Module &M);

  /// Forward: propagate sign from a def to its result.
  bool propagateForward(llvm::Instruction &I);

  /// Backward: propagate sign constraints from a use to its operands.
  bool propagateBackward(llvm::Instruction &I);
};

} // namespace smack

#endif // SIGNANALYSIS_H
