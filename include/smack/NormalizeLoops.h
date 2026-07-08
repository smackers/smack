//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef NORMALIZELOOPS_H
#define NORMALIZELOOPS_H

#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include <map>

namespace smack {

class NormalizeLoops : public llvm::LoopPass {
public:
  static char ID; // Pass identification, replacement for typeid
  NormalizeLoops() : llvm::LoopPass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnLoop(llvm::Loop *L, llvm::LPPassManager &LPM) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage &) const override;
};
} // namespace smack

#endif // NORMALIZELOOPS_H
