//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKGENERATOR_H
#define SMACKGENERATOR_H

#include "Block.h"
#include "SmackInstVisitor.h"
#include "SmackModule.h"
#include "BplPrintUtils.h"
#include "llvm/Function.h"
#include "llvm/InstrTypes.h"
#include "llvm/Pass.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CFG.h"
#include "llvm/Target/TargetData.h"
#include <map>
#include <stack>
#include <vector>

using namespace llvm;

namespace smack {

class SmackGenerator : public ModulePass {
private:
  SmackModule* module;

public:
  static char ID; // Pass identification, replacement for typeid

  SmackGenerator() : ModulePass(ID) {}
  virtual bool runOnModule(Module &m);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<TargetData>();
  }

  SmackModule* getModule() const {
    return module;
  }
};
}

#endif  /*SMACKGENERATOR_H*/
