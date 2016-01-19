//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef MEMORYALLOCATIONCHECKER_H
#define MEMORYALLOCATIONCHECKER_H

#include "llvm/Pass.h"

namespace smack {
  class MemoryAllocationChecker: public llvm::ModulePass {
    //private:
      //llvm::raw_ostream &out;
    public:
      static char ID; // Pass identification, replacement for typeid
      //MemoryAllocationChecker(llvm::raw_ostream &out) : llvm::ModulePass(ID), out(out) {}
      MemoryAllocationChecker() : llvm::ModulePass(ID) {}
      virtual bool runOnModule(llvm::Module& m);
  };
}

#endif //MEMORYALLOCATIONCHECKER_H
