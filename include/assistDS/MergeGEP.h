//===-- MergeGEP.cpp - Merge GEPs for indexing in arrays ------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Merge chained GEPs; Specially useful for arrays inside structs
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: MergeArrayGEP
  //
  class MergeArrayGEP : public ModulePass {
  public:
    static char ID;
    MergeArrayGEP() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

