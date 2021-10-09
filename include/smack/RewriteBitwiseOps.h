//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REWRITEBITWISEOPS_H
#define REWRITEBITWISEOPS_H

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace smack {

class RewriteBitwiseOps : public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  RewriteBitwiseOps() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnModule(llvm::Module &m) override;
};
} // namespace smack

#endif // REWRITEBITWISEOPS_H
