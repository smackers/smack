//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include <utility>
#include <vector>

namespace smack {

class SplitAggregateValue : public llvm::BasicBlockPass {
public:
  typedef std::vector<std::pair<llvm::Value *, unsigned>> IndexT;
  typedef std::pair<IndexT, llvm::Constant *> InfoT;
  static char ID;
  SplitAggregateValue() : llvm::BasicBlockPass(ID) {}
  virtual bool runOnBasicBlock(llvm::BasicBlock &BB);

private:
  llvm::Value *splitAggregateLoad(llvm::LoadInst *li, std::vector<InfoT> &info,
                                  llvm::IRBuilder<> &irb);
  void splitAggregateStore(llvm::StoreInst *si, std::vector<InfoT> &info,
                           llvm::IRBuilder<> &irb);
  void splitConstantReturn(llvm::ReturnInst *ri, std::vector<InfoT> &info);
  void splitConstantArg(llvm::CallInst *ci, unsigned i,
                        std::vector<InfoT> &info);
  void visitAggregateValue(llvm::Constant *baseVal, llvm::Type *T, IndexT idxs,
                           std::vector<InfoT> &info, llvm::LLVMContext &C);
  llvm::Value *createInsertedValue(llvm::IRBuilder<> &irb, llvm::Type *T,
                                   std::vector<InfoT> &info, llvm::Value *V);
  bool isConstantAggregate(llvm::Value *V);
};
}
