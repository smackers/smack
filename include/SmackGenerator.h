//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKGENERATOR_H
#define SMACKGENERATOR_H

#include "BoogieAst.h"

#include "SmackInstVisitor.h"
#include "BplPrintUtils.h"
#include "llvm/Function.h"
#include "llvm/InstrTypes.h"
#include "llvm/Pass.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CFG.h"
#include "llvm/DataLayout.h"
#include <map>
#include <stack>
#include <vector>

namespace smack {

class SmackGenerator : public llvm::ModulePass {
private:
  Program *program;

public:
  static char ID; // Pass identification, replacement for typeid

  SmackGenerator() : ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &m);

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<llvm::DataLayout>();
  }
  
  Program * getProgram() const { return program; }
};
}

#endif  /*SMACKGENERATOR_H*/
