//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef RUSTFIXES_H
#define RUSTFIXES_H

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace smack {

namespace detail {
// Shared body for the RustFixes transform. Both the legacy FunctionPass and
// the NewPM sibling delegate here so behavior stays in lock-step during the
// LegacyPM -> NewPM migration (Phase A5).
bool runRustFixes(llvm::Function &F);
} // namespace detail

class RustFixes : public llvm::FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  RustFixes() : llvm::FunctionPass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnFunction(llvm::Function &F) override;
};

class RustFixesNewPM : public llvm::PassInfoMixin<RustFixesNewPM> {
public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &);
  static llvm::StringRef name() { return "RustFixesNewPM"; }
};

} // namespace smack

#endif // RUSTFIXES_H
