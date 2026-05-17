//
// This file is distributed under the MIT License. See LICENSE for details.
//
// Promote disconnected uninitialized-local undefs into a single named
// nondet so the verifier sees one variable per C local instead of one
// per LLVM use.
//
#ifndef INIT_UNDEF_ALLOCAS_H
#define INIT_UNDEF_ALLOCAS_H

#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {
class AnalysisUsage;
}

namespace smack {

namespace detail {
// Shared body. Takes the DominatorTree as a parameter so the legacy
// FunctionPass wrapper and the NewPM sibling can each obtain it from their
// own analysis manager.
bool runInitUndefAllocas(llvm::Function &F, llvm::DominatorTree &DT);
} // namespace detail

class InitUndefAllocas : public llvm::FunctionPass {
public:
  static char ID;
  InitUndefAllocas() : llvm::FunctionPass(ID) {}

  bool runOnFunction(llvm::Function &F) override;

  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

  llvm::StringRef getPassName() const override {
    return "InitUndefAllocas";
  }
};

class InitUndefAllocasNewPM
    : public llvm::PassInfoMixin<InitUndefAllocasNewPM> {
public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &FAM);
  static llvm::StringRef name() { return "InitUndefAllocasNewPM"; }
};

} // namespace smack

#endif // INIT_UNDEF_ALLOCAS_H
