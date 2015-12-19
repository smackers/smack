//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef MEMORYALLOCATIONCHECKER_H
#define MEMORYALLOCATIONCHECKER_H

#include "llvm/Pass.h"

namespace smack {
  class MemoryAllocationChecker: public llvm::ModulePass {
    public:
      static char ID; // Pass identification, replacement for typeid
      MemoryAllocationChecker() : llvm::ModulePass(ID) {}
      virtual bool runOnModule(llvm::Module& m);
  };
}

#endif //MEMORYALLOCATIONCHECKER_H
