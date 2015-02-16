//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKMODULEGENERATOR_H
#define SMACKMODULEGENERATOR_H

#include "smack/BoogieAst.h"
#include "smack/SmackInstGenerator.h"
#include "smack/DSAAliasAnalysis.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/CFG.h"
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

  SmackModuleGenerator() : ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage& AU) const {
    AU.setPreservesAll();
    AU.addRequired<llvm::DataLayoutPass>();
    AU.addRequired<DSAAliasAnalysis>();
  }

  virtual bool runOnModule(llvm::Module& m) {
    generateProgram(m);
    return false;
  }
  
  void generateProgram(llvm::Module& m);

  Program& getProgram() {
    return program;
  }
};
}

#endif // SMACKMODULEGENERATOR_H

