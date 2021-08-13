//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef PROMOTEMEMCPY_H
#define PROMOTEMEMCPY_H

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Pass.h"

#include <vector>
namespace smack {

class PromoteMemcpy : public llvm::FunctionPass {
  bool tryPromote(llvm::MemCpyInst *, std::vector<llvm::Instruction *> &);
  const llvm::DataLayout *DL;

public:
  static char ID; // Pass identification, replacement for typeid
  PromoteMemcpy() : llvm::FunctionPass(ID) {}
  virtual llvm::StringRef getPassName() const;
  virtual bool runOnFunction(llvm::Function &F);
};
} // namespace smack

#endif // PROMOTEMEMCPY_H
