//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace smack {

using namespace llvm;

class ExtractContracts : public ModulePass {
public:
  static char ID;
  ExtractContracts() : ModulePass(ID) {}
  virtual bool runOnModule(Module &M) override;
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
};
} // namespace smack
