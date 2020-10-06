//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REMOVEUNUSEDFUNCTIONS_H
#define REMOVEUNUSEDFUNCTIONS_H

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace smack {

class RemoveUnusedFunctions : public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  RemoveUnusedFunctions() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnModule(llvm::Module &m) override;
};
} // namespace smack

#endif // REMOVEUNUSEDFUNCTIONS_H
