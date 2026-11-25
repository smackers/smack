//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef MEMORYSAFETYCHECKER_H
#define MEMORYSAFETYCHECKER_H

#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include <map>

namespace smack {

class MemorySafetyChecker : public llvm::FunctionPass,
                            public llvm::InstVisitor<MemorySafetyChecker> {
private:
  llvm::Function *getLeakCheckFunction(llvm::Module &M);
  llvm::Function *getSafetyCheckFunction(llvm::Module &M);

  void copyDbgMetadata(llvm::Instruction *src, llvm::Instruction *dst);
  void insertMemoryLeakCheck(llvm::Instruction *I);
  void insertMemoryAccessCheck(llvm::Value *addr, llvm::Value *size,
                               llvm::Instruction *I);
  bool visitSplitAggregateAccess(llvm::Value *addr, llvm::Instruction *I);

public:
  static char ID; // Pass identification, replacement for typeid
  MemorySafetyChecker() : llvm::FunctionPass(ID) {}
  virtual bool runOnFunction(llvm::Function &F) override;

  // Memory-access checks are compiler-inserted calls.  Keep their provenance
  // explicit so later exact transformations never trust the reserved callee
  // name or try to recover the protected access from instruction adjacency.
  static const llvm::Instruction *
  getCheckedInstruction(const llvm::CallInst &I);

  void visitReturnInst(llvm::ReturnInst &I);
  void visitLoadInst(llvm::LoadInst &I);
  void visitStoreInst(llvm::StoreInst &I);
  void visitMemSetInst(llvm::MemSetInst &I);
  void visitMemTransferInst(llvm::MemTransferInst &I);
};
} // namespace smack

#endif // MEMORYSAFETYCHECKER_H
