//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/IR/IRBuilder.h"

#include <vector>
#include <utility>

namespace smack {

class SplitAggregateLoadStore : public llvm::BasicBlockPass {
public:
  static char ID;

  SplitAggregateLoadStore() : llvm::BasicBlockPass(ID) {}
  virtual bool runOnBasicBlock(llvm::BasicBlock& BB);

private:
  void splitAggregateLoad(llvm::LoadInst* li);
  llvm::Value* buildAggregateValues(llvm::IRBuilder<> *irb, llvm::Value* ptr, llvm::Type* ct,
      llvm::Value* val, std::vector<std::pair<llvm::Value*, unsigned>> idxs);
  void splitAggregateStore(llvm::StoreInst* si, llvm::Value* ptr, llvm::Value* val);
  void copyAggregateValues(llvm::IRBuilder<> *irb, llvm::Value* ptr, llvm::Type* ct,
      llvm::Value* val, std::vector<std::pair<llvm::Value*, unsigned>> idxs);
};
}
