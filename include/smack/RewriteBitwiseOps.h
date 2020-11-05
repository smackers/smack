//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef CONSTANTBVOPS_H
#define CONSTANTBVOPS_H

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"

namespace smack {

class RewriteBitwiseOps : public llvm::FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  RewriteBitwiseOps() : llvm::FunctionPass(ID) {}
  virtual llvm::StringRef getPassName() const;
  virtual bool runOnFunction(llvm::Function &f);
};
} // namespace smack

#endif // CONSTANTBVOPS_H
