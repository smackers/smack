//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLPRINTER_H
#define BPLPRINTER_H

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace smack {

class BplPrinter : public llvm::ModulePass {

public:
  static char ID; // Pass identification, replacement for typeid

  BplPrinter() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &m) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
};

class BplPrinterNewPM : public llvm::PassInfoMixin<BplPrinterNewPM> {
public:
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
  static llvm::StringRef name() { return "BplPrinterNewPM"; }
};
} // namespace smack

#endif // BPLPRINTER_H
