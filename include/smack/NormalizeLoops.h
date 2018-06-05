//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef NORMALIZELOOPS_H
#define NORMALIZELOOPS_H

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include <map>

namespace smack {

class NormalizeLoops: public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  NormalizeLoops() : llvm::ModulePass(ID) {}
  const char* getPassName() const override;
  virtual bool runOnModule(llvm::Module& m) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage&) const override;
};
}

#endif //NORMALIZELOOPS_H
