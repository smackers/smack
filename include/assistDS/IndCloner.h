//===-- IndCloner.h - Clone Indirectly Called Functions -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This code defines a pass which clones functions which could potentially be
// used in indirect function calls.
//
//===----------------------------------------------------------------------===//

#include "llvm/Instructions.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"

namespace llvm {
  //
  // Class: IndClone
  //
  // Description:
  //  Implement an LLVM pass that clones functions which could be used for
  //  indirect function calls.
  //
  class IndClone : public ModulePass {
  public:
    static char ID;
    IndClone() : ModulePass(ID) {}
    virtual bool runOnModule(Module& M);
  };
}

