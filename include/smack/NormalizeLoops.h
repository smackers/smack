//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef NORMALIZELOOPS_H
#define NORMALIZELOOPS_H

#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include <map>

namespace llvm {
class LoopInfo;
}

namespace smack {

namespace detail {
// Shared body. Caller supplies a getter that returns the per-function
// LoopInfo so the legacy ModulePass and NewPM sibling can each fetch from
// their own analysis manager.
bool runNormalizeLoops(
    llvm::Module &M,
    llvm::function_ref<llvm::LoopInfo &(llvm::Function &)> getLoopInfo);
} // namespace detail

class NormalizeLoops : public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  NormalizeLoops() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnModule(llvm::Module &m) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage &) const override;
};

class NormalizeLoopsNewPM : public llvm::PassInfoMixin<NormalizeLoopsNewPM> {
public:
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
  static llvm::StringRef name() { return "NormalizeLoopsNewPM"; }
};
} // namespace smack

#endif // NORMALIZELOOPS_H
