//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SIGNEDINTEGEROVERFLOWCHECKER_H
#define SIGNEDINTEGEROVERFLOWCHECKER_H

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include <map>

namespace smack {
  
class SignedIntegerOverflowChecker: public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  SignedIntegerOverflowChecker() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module& m);
private:
  static std::map<std::string, llvm::Instruction::BinaryOps> INSTRUCTION_TABLE;
  static std::map<int, std::string> INT_MAX_TABLE;
  static std::map<int, std::string> INT_MIN_TABLE;
  void replaceValue(llvm::Value* ee, llvm::Value* er);
};

}

#endif //SIGNEDINTEGEROVERFLOWCHECKER_H
