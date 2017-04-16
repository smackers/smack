//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/IR/IRBuilder.h"

#include <vector>

namespace smack {

class SplitStructLoadStore : public llvm::ModulePass {
public:
  static char ID;

  SplitStructLoadStore() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module& M);
private:
  const llvm::DataLayout* DL;
  std::vector<llvm::Instruction*> toRemove;

  void splitStructStore(llvm::StoreInst* si, llvm::Value* ptr, llvm::Value* val);
  void copyStructs(llvm::IRBuilder<> *irb, llvm::Value* ptr, llvm::Constant* val, std::vector<llvm::Value*> idxs);
};
}
