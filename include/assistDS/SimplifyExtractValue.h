//===-- SimplifyExtractValue.cpp - Remove extraneous extractvalue insts----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Simplify extractvalue
//
// Derived from InstCombine
//
//===----------------------------------------------------------------------===//

#include "llvm/Instructions.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: SimplifyEV
  //
  class SimplifyEV : public ModulePass {
  public:
    static char ID;
    SimplifyEV() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

