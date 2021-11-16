//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef LOOPINFO_H
#define LOOPINFO_H

#include "llvm/Pass.h"

namespace smack {

class LoopInfo : public llvm::FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  LoopInfo() : llvm::FunctionPass(ID) {}
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnFunction(llvm::Function &F) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage &) const override;
};
} // namespace smack

#endif // LOOPINFO_H
