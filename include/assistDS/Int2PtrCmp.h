//===-- Int2PtrCmp.cpp - Merge inttoptr/ptrtoint --------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Remove unnecessary inttoptr casts
// Specially ones used in just compares
// Most cases derived from InstCombine
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"


namespace llvm {
  //
  // Class: Int2PtrCmp
  //
  //
  class Int2PtrCmp : public ModulePass {
  private:
    const DataLayout * TD;
  public:
    static char ID;
    Int2PtrCmp() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

