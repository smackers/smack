//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef INTEGEROVERFLOWCHECKER_H
#define INTEGEROVERFLOWCHECKER_H

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include <map>

namespace smack {

class IntegerOverflowChecker : public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  IntegerOverflowChecker() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnModule(llvm::Module &m) override;

  // Shared body — also called by IntegerOverflowCheckerNewPM. The body has no
  // dependency on instance state; promoted to `static` during Phase A5.
  static bool runImpl(llvm::Module &m);

private:
  static const std::map<std::string, llvm::Instruction::BinaryOps>
      INSTRUCTION_TABLE;
  static llvm::APInt getMax(unsigned bits, bool isSigned);
  static llvm::APInt getMin(unsigned bits, bool isSigned);
  static llvm::Value *extendBitWidth(llvm::Value *v, int bits, bool isSigned,
                                     llvm::Instruction *i);
  static llvm::BinaryOperator *createFlag(llvm::Value *v, int bits, bool isSigned,
                                          llvm::Instruction *i);
  static llvm::Value *createResult(llvm::Value *v, int bits, llvm::Instruction *i);
  static void addCheck(llvm::Function *co, llvm::Value *flag,
                       llvm::Instruction *i);
  static void addBlockingAssume(llvm::Function *va, llvm::Value *flag,
                                llvm::Instruction *i);
};

class IntegerOverflowCheckerNewPM
    : public llvm::PassInfoMixin<IntegerOverflowCheckerNewPM> {
public:
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
  static llvm::StringRef name() { return "IntegerOverflowCheckerNewPM"; }
};
} // namespace smack

#endif // INTEGEROVERFLOWCHECKER_H
