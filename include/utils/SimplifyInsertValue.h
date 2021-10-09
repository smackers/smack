//===-- SimplifyInsertValue.cpp - Remove extraneous insertvalue insts------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Simplify insertvalue
// Replace insertvalue by storess where possible
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: SimplifyIV
  //
  class SimplifyIV : public ModulePass {
  public:
    static char ID;
    SimplifyIV() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

