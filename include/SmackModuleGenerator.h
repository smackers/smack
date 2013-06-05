//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKGENERATOR_H
#define SMACKGENERATOR_H

#include "BoogieAst.h"
#include "llvm/DataLayout.h"

namespace smack {

    class SmackModuleGenerator : public llvm::ModulePass {
    private:
      Program *program;

    public:
      static char ID; // Pass identification, replacement for typeid

      SmackModuleGenerator() : ModulePass(ID) {}
      virtual bool runOnModule(llvm::Module &m);

      virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<llvm::DataLayout>();
      }
  
      Program * getProgram() const { return program; }
    };
}

#endif  /*SMACKGENERATOR_H*/
