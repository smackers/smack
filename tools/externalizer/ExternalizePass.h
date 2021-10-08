//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef EXTERNALIZEPASS_H
#define EXTERNALIZEPASS_H

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

namespace externalize {
struct ExternalizePass : public llvm::ModulePass {
  static char ID;
  ExternalizePass() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnModule(llvm::Module &M) override;
};
} // namespace externalize
#endif // EXTERNALIZEPASS_H
