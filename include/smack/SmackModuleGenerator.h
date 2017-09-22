//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKMODULEGENERATOR_H
#define SMACKMODULEGENERATOR_H

#include "llvm/Pass.h"

namespace smack {

class Program;

class SmackModuleGenerator : public llvm::ModulePass {
private:
  Program* program;

public:
  static char ID; // Pass identification, replacement for typeid

  SmackModuleGenerator();
  virtual void getAnalysisUsage(llvm::AnalysisUsage& AU) const;
  virtual bool runOnModule(llvm::Module& m);
  void generateProgram(llvm::Module& m);
  Program* getProgram() {
    return program;
  }
};
}

#endif // SMACKMODULEGENERATOR_H
