//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef FUNCTIONALLOOPSUMMARY_H
#define FUNCTIONALLOOPSUMMARY_H

#include "llvm/ADT/SmallVector.h"
#include <cstdint>
#include <vector>

namespace llvm {
class AAResults;
class BasicBlock;
class BranchInst;
class CallInst;
class Function;
class IntegerType;
class ConstantInt;
class LoadInst;
class Loop;
class LoopInfo;
class MemorySSA;
class PHINode;
class SCEV;
class ScalarEvolution;
class StoreInst;
class Value;
} // namespace llvm

namespace smack {

struct AffineLoopAccess {
  const llvm::SCEV *start = nullptr;
  const llvm::Value *base = nullptr;
  uint64_t offset = 0;
  uint64_t stride = 0;
  bool hasConstantOffset = false;
};

struct FunctionalLoopLoad {
  const llvm::LoadInst *load = nullptr;
  AffineLoopAccess access;
};

struct FunctionalLoopStore {
  const llvm::StoreInst *store = nullptr;
  AffineLoopAccess access;
  const llvm::Value *guard = nullptr;
  bool guardValue = true;
};

struct FunctionalLoopScalarRecurrence {
  const llvm::Value *value = nullptr;
  const llvm::ConstantInt *start = nullptr;
  const llvm::ConstantInt *step = nullptr;
};

struct FunctionalLoopVerifierAction {
  enum class Kind { Assertion, Assumption };

  Kind kind = Kind::Assertion;
  const llvm::Value *predicateValue = nullptr;
  llvm::CallInst *call = nullptr;
  const llvm::BranchInst *predicateBranch = nullptr;
  bool continueConditionValue = true;
  bool predicateIsNonzero = false;
};

// Analysis-only description of a pointwise loop.  It deliberately contains
// LLVM values rather than Boogie expressions so recognition and emission stay
// separate and the emitter can use SMACK's actual memory representation.
struct FunctionalLoopSummary {
  enum class Kind { MemoryUpdate, ReadOnlyPredicate, ReadOnlyVerifier };

  Kind kind = Kind::MemoryUpdate;
  llvm::Loop *loop = nullptr;
  llvm::BasicBlock *preheader = nullptr;
  llvm::BasicBlock *exit = nullptr;
  llvm::PHINode *induction = nullptr;
  const llvm::Value *inductionStart = nullptr;
  const llvm::ConstantInt *inductionStep = nullptr;
  bool inductionEscapes = false;
  llvm::IntegerType *iterationType = nullptr;
  const llvm::SCEV *iterationCount = nullptr;
  llvm::SmallVector<FunctionalLoopStore, 2> stores;
  llvm::SmallVector<FunctionalLoopLoad, 2> loads;
  llvm::SmallVector<FunctionalLoopScalarRecurrence, 2> recurrences;
  llvm::SmallVector<FunctionalLoopVerifierAction, 2> verifierActions;
  llvm::SmallVector<llvm::PHINode *, 1> finalInductionPhis;
  const llvm::BranchInst *predicateBranch = nullptr;
  const llvm::Value *predicateValue = nullptr;
  llvm::BasicBlock *normalExit = nullptr;
  llvm::BasicBlock *failureExit = nullptr;
  bool continueConditionValue = true;
};

class FunctionalLoopSummaryAnalysis {
public:
  static std::vector<FunctionalLoopSummary>
  analyze(llvm::Function &F, llvm::LoopInfo &LI, llvm::ScalarEvolution &SE,
          llvm::AAResults &AA, llvm::MemorySSA &MSSA);
};

} // namespace smack

#endif // FUNCTIONALLOOPSUMMARY_H
