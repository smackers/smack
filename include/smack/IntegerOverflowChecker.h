//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef INTEGEROVERFLOWCHECKER_H
#define INTEGEROVERFLOWCHECKER_H

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include <map>

namespace smack {

class IntegerOverflowChecker : public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  IntegerOverflowChecker() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnModule(llvm::Module &m) override;

private:
  static const std::map<std::string, llvm::Instruction::BinaryOps>
      INSTRUCTION_TABLE;
  std::string getMax(unsigned bits, bool isSigned);
  std::string getMin(unsigned bits, bool isSigned);
  llvm::Value *extendBitWidth(llvm::Value *v, int bits, bool isSigned,
                              llvm::Instruction *i);
  llvm::BinaryOperator *createFlag(llvm::Value *v, int bits, bool isSigned,
                                   llvm::Instruction *i);
  llvm::Value *createResult(llvm::Value *v, int bits, llvm::Instruction *i);
  void addCheck(llvm::Function *co, llvm::Value *flag, llvm::Instruction *i);
  void addBlockingAssume(llvm::Function *va, llvm::Value *flag,
                         llvm::Instruction *i);
};
} // namespace smack

#endif // INTEGEROVERFLOWCHECKER_H
