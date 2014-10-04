//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLPRINTER_H
#define BPLPRINTER_H

#include "smack/SmackModuleGenerator.h"

namespace smack {

class BplPrinter : public llvm::ModulePass {

public:
  static char ID; // Pass identification, replacement for typeid

  BplPrinter() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module& m);
  virtual void getAnalysisUsage(llvm::AnalysisUsage& AU) const {
    AU.setPreservesAll();
    AU.addRequired<SmackModuleGenerator>();
  }
};
}

#endif // BPLPRINTER_H

