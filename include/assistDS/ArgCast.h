//===-------- ArgCast.cpp - Cast Arguments to Calls -----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
// Convert
// call(bitcast (.., T1 arg, ...)F to(..., T2 arg, ...))(..., T2 val, ...)
// to
// val1 = bitcast T2 val to T1
// call F (..., T1 val1, ...)
//===----------------------------------------------------------------------===//

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: ArgCast
  //
  // Description:
  //  Implement an LLVM pass that cleans up call sites that take casted args
  //
  class ArgCast : public ModulePass {
  public:
    static char ID;
    ArgCast() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

