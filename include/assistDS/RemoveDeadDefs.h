//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace llvm {
class RemoveDeadDefs : public ModulePass {
private:
  const DataLayout * TD;
public:
  static char ID;
  RemoveDeadDefs() : ModulePass(ID) {}
  virtual bool runOnModule(Module& M);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<DataLayoutPass>();
  }
};
}
