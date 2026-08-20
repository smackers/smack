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
class Function;
class IntegerType;
class LoadInst;
class Loop;
class LoopInfo;
class MemorySSA;
class PHINode;
class ScalarEvolution;
class StoreInst;
class Value;
} // namespace llvm

namespace smack {

struct AffineLoopAccess {
  const llvm::Value *base = nullptr;
  uint64_t stride = 0;
};

struct FunctionalLoopLoad {
  const llvm::LoadInst *load = nullptr;
  AffineLoopAccess access;
};

// Analysis-only description of a pointwise loop.  It deliberately contains
// LLVM values rather than Boogie expressions so recognition and emission stay
// separate and the emitter can use SMACK's actual memory representation.
struct FunctionalLoopSummary {
  llvm::Loop *loop = nullptr;
  llvm::BasicBlock *preheader = nullptr;
  llvm::BasicBlock *exit = nullptr;
  llvm::PHINode *induction = nullptr;
  llvm::IntegerType *iterationType = nullptr;
  const llvm::Value *iterationCount = nullptr;
  const llvm::StoreInst *store = nullptr;
  AffineLoopAccess write;
  llvm::SmallVector<FunctionalLoopLoad, 2> loads;
};

class FunctionalLoopSummaryAnalysis {
public:
  static std::vector<FunctionalLoopSummary>
  analyze(llvm::Function &F, llvm::LoopInfo &LI, llvm::ScalarEvolution &SE,
          llvm::AAResults &AA, llvm::MemorySSA &MSSA);
};

} // namespace smack

#endif // FUNCTIONALLOOPSUMMARY_H
