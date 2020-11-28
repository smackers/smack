//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef RUSTFIXES_H
#define RUSTFIXES_H

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace smack {

class RustFixes : public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  RustFixes() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const;
  virtual bool runOnModule(llvm::Module &m);
};
} // namespace smack

#endif // RUSTFIXES_H
