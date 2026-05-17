//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLFILEPRINTER_H
#define BPLFILEPRINTER_H

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

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

class BplFilePrinterNewPM : public llvm::PassInfoMixin<BplFilePrinterNewPM> {
private:
  llvm::raw_ostream &out;

public:
  explicit BplFilePrinterNewPM(llvm::raw_ostream &out) : out(out) {}
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
  static llvm::StringRef name() { return "BplFilePrinterNewPM"; }
};
} // namespace smack

#endif // BPLPRINTER_H
