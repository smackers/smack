//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLPRINTER_H
#define BPLPRINTER_H

#include "SmackGenerator.h"
#include "llvm/Function.h"
#include "llvm/InstrTypes.h"
#include "llvm/Pass.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CFG.h"

using namespace llvm;

namespace smack {

class BplPrinter : public ModulePass {

public:
  static char ID; // Pass identification, replacement for typeid

  BplPrinter() : ModulePass(ID) {}
  virtual bool runOnModule(Module &m);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<SmackGenerator>();
  }
};
}

#endif  /*BPLPRINTER_H*/
