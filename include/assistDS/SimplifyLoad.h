//===--------------- SimplifyLoad.cpp - Simplify load insts ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Derived from InstCombine
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: SimplifyLoad
  //
  class SimplifyLoad : public ModulePass {
  public:
    static char ID;
    SimplifyLoad() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

