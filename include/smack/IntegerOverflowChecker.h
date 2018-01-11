//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef INTEGEROVERFLOWCHECKER_H
#define INTEGEROVERFLOWCHECKER_H

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
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
  void replaceValue(llvm::Value* ee, llvm::Value* er);
};

}

#endif //INTEGEROVERFLOWCHECKER_H
