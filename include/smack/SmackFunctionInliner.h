//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef SMACKFUNCTIONINLINER_H
#define SMACKFUNCTIONINLINER_H

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include <set>

namespace smack {

class SmackFunctionInliner : public llvm::ModulePass {
public:
  static char ID;
  SmackFunctionInliner() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M) override;

private:
  bool shouldInline(llvm::Function &F);
  bool involvesPointers(llvm::Function &F);
  unsigned getInstructionCount(llvm::Function &F);
  void computeRecursiveFunctions(llvm::Module &M);

  std::set<llvm::Function *> recursiveFunctions;
};

} // namespace smack

#endif // SMACKFUNCTIONINLINER_H
