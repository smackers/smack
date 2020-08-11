//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef ANNOTATELOOPEXITS_H
#define ANNOTATELOOPEXITS_H

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include <map>

namespace smack {

class AnnotateLoopExits : public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  AnnotateLoopExits() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnModule(llvm::Module &m) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage &) const override;
};
} // namespace smack

#endif // ANNOTATELOOPEXITS_H
