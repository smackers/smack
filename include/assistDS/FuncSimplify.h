//===-------- ArgCast.cpp - Cast Arguments to Calls -----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: FuncSimplify
  //
  // Description:
  //  Replace all internal aliases with the
  //  aliasee value
  //
  class FuncSimplify : public ModulePass {
  public:
    static char ID;
    FuncSimplify() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

