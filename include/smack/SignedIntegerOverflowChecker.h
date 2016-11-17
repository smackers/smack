//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SIGNEDINTEGEROVERFLOWCHECKER_H
#define SIGNEDINTEGEROVERFLOWCHECKER_H

#include "llvm/Pass.h"

namespace smack {
  
class SignedIntegerOverflowChecker: public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  SignedIntegerOverflowChecker() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module& m);
};

}

#endif //SIGNEDINTEGEROVERFLOWCHECKER_H
