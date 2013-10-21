//===--------------- SimplifyGEP.cpp - Simplify GEPs types  ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Simplify GEPs with bitcasts (mostly cloned from InstCombine)
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: SimplifyGEP
  //
  class SimplifyGEP : public ModulePass {
  private:
    DataLayout * TD;
  public:
    static char ID;
    SimplifyGEP() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<DataLayout>();
    }
  };
}

