//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef INTEGEROVERFLOWCHECKER_H
#define INTEGEROVERFLOWCHECKER_H

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include <map>

namespace smack {
  
class IntegerOverflowChecker: public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  const char* getPassName() const;
  IntegerOverflowChecker() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module& m);
private:
  static const std::map<std::string, llvm::Instruction::BinaryOps> INSTRUCTION_TABLE;
  llvm::Value* extValue(llvm::Value* v, int bits, bool isSigned, llvm::Instruction* i, bool check = true);
  llvm::BinaryOperator* mkFlag(llvm::Value* v, int bits, bool isSigned, llvm::Instruction* i, bool check = true);
  llvm::Value* mkResult(llvm::Value* v, int bits, llvm::Instruction* i, bool check = true);
  void mkCheck(llvm::Function* co, llvm::BinaryOperator* flag, llvm::Instruction* i);
  void mkBlockingAssume(llvm::Function* va, llvm::BinaryOperator* flag, llvm::Instruction* i);
};
}

#endif //INTEGEROVERFLOWCHECKER_H
