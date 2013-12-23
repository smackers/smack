//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKMODULEGENERATOR_H
#define SMACKMODULEGENERATOR_H

#include "smack/BoogieAst.h"
#include "smack/SmackInstGenerator.h"
#include "smack/DSAAliasAnalysis.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"
#include <sstream>
#include <stack>

using namespace std;
using llvm::errs;

namespace smack {

class SmackModuleGenerator : public llvm::ModulePass {
private:
  Program program;

public:
  static char ID; // Pass identification, replacement for typeid

  SmackModuleGenerator() : ModulePass(ID), program("") {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage& AU) const {
    AU.setPreservesAll();
    AU.addRequired<llvm::DataLayout>();
    AU.addRequired<DSAAliasAnalysis>();
  }

  virtual bool runOnModule(llvm::Module& m) {  
    SmackRep* rep = SmackRep::createRep(&getAnalysis<DSAAliasAnalysis>());
    generateProgram(m,rep);
    return false;
  }
  
  void generateProgram(llvm::Module& m, SmackRep* rep);

  Program& getProgram() {
    return program;
  }
};
}

#endif // SMACKMODULEGENERATOR_H

