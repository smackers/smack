//===-- LoadArgs.cpp - Promote args if they came from loads ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Identify calls, that are passed arguemtns that are LoadInsts.
// Pass the original pointer instead. Helps improve some
// context sensitivity.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: LoadArgs
  //
  // Description:
  //  Implement an LLVM pass that clones functions which are passed loads
  //  as an argument
  //  
  //
  class LoadArgs : public ModulePass {
  public:
    static char ID;
    LoadArgs() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

