//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLFILEPRINTER_H
#define BPLFILEPRINTER_H

#include "smack/SmackModuleGenerator.h"

namespace smack {

class BplFilePrinter : public llvm::ModulePass {
private:
  llvm::raw_ostream &out;
  
public:
  static char ID; // Pass identification, replacement for typeid

  BplFilePrinter(llvm::raw_ostream &out) : llvm::ModulePass(ID), out(out) {}
  
  virtual bool runOnModule(llvm::Module& m);
  
  virtual const char *getPassName() const {
    return "Boogie file printing";
  }
  
  virtual void getAnalysisUsage(llvm::AnalysisUsage& AU) const {
    AU.setPreservesAll();
    AU.addRequired<SmackModuleGenerator>();
  } 
};
}

#endif // BPLPRINTER_H

