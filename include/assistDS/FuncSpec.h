//===-- FuncSpec.cpp - Clone Functions With Constant Function Ptr Args ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass clones functions that take constant function pointers as arguments
// from some call sites. It changes those call sites to call cloned functions.
//
//===----------------------------------------------------------------------===//

#include "llvm/Instructions.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: FuncSpec
  //
  // Description:
  //  Implement an LLVM pass that clones functions which are passed
  //  as an argument
  //  
  //
  class FuncSpec : public ModulePass {
  public:
    static char ID;
    FuncSpec() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

