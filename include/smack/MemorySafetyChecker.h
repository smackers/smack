//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef MEMORYSAFETYCHECKER_H
#define MEMORYSAFETYCHECKER_H

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstVisitor.h"
#include <map>

namespace smack {

class MemorySafetyChecker: public llvm::FunctionPass, public llvm::InstVisitor<MemorySafetyChecker> {
private:
  std::map<llvm::Module*, llvm::Function*> leakCheckFunction;
  std::map<llvm::Module*, llvm::Function*> safetyCheckFunction;

  llvm::Function* getLeakCheckFunction(llvm::Module& M);
  llvm::Function* getSafetyCheckFunction(llvm::Module& M);

  void insertMemoryLeakCheck(llvm::Instruction* I);
  void insertMemoryAccessCheck(llvm::Value* addr, llvm::Value* size, llvm::Instruction* I);

public:
  static char ID; // Pass identification, replacement for typeid
  MemorySafetyChecker() : llvm::FunctionPass(ID) {}
  virtual bool runOnFunction(llvm::Function& F);

  void visitReturnInst(llvm::ReturnInst& I);
  void visitLoadInst(llvm::LoadInst& I);
  void visitStoreInst(llvm::StoreInst& I);
  void visitMemSetInst(llvm::MemSetInst& I);
  void visitMemTransferInst(llvm::MemTransferInst& I);
};

}

#endif //MEMORYSAFETYCHECKER_H
