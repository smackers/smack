//===-------- StructReturnToPointer.cpp ------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// For functions that return structures,
// transform them to return a pointer to the structure instead.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: StructRet
  //
  class StructRet : public ModulePass {
  public:
    static char ID;
    StructRet() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

