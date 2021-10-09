//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLFILEPRINTER_H
#define BPLFILEPRINTER_H

#include "llvm/Pass.h"

namespace smack {

class BplFilePrinter : public llvm::ModulePass {
private:
  llvm::raw_ostream &out;

public:
  static char ID; // Pass identification, replacement for typeid

  BplFilePrinter(llvm::raw_ostream &out) : llvm::ModulePass(ID), out(out) {}

  virtual bool runOnModule(llvm::Module &m) override;

  virtual llvm::StringRef getPassName() const override {
    return "Boogie file printing";
  }

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
};
} // namespace smack

#endif // BPLPRINTER_H
