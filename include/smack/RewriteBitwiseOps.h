//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REWRITEBITWISEOPS_H
#define REWRITEBITWISEOPS_H

#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace smack {

namespace detail {
// Shared body for the RewriteBitwiseOps transform. Both the legacy
// ModulePass wrapper and the NewPM sibling delegate here so behavior stays
// in lock-step during the LegacyPM -> NewPM migration (Phase A5).
bool runRewriteBitwiseOps(llvm::Module &M);
} // namespace detail

class RewriteBitwiseOps : public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  RewriteBitwiseOps() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnModule(llvm::Module &m) override;
};

class RewriteBitwiseOpsNewPM
    : public llvm::PassInfoMixin<RewriteBitwiseOpsNewPM> {
public:
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
  static llvm::StringRef name() { return "RewriteBitwiseOpsNewPM"; }
};
} // namespace smack

#endif // REWRITEBITWISEOPS_H
