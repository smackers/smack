//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef CONSTANTBVOPS_H
#define CONSTANTBVOPS_H

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include <map>

namespace smack {

class ConstantBVOps : public llvm::FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  ConstantBVOps() : llvm::FunctionPass(ID) {}
  virtual llvm::StringRef getPassName() const;
  virtual bool runOnFunction(llvm::Function &f);
};
} // namespace smack

#endif // CONSTANTBVOPS_H
