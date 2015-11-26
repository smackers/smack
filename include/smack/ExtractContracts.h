//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace smack {

using namespace llvm;

class ExtractContracts : public ModulePass, public InstVisitor<ExtractContracts> {
private:
  const llvm::DataLayout * TD;
public:
  static char ID;
  ExtractContracts() : ModulePass(ID) {}
  virtual bool runOnModule(Module& M);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<DataLayoutPass>();
  }
  void visitCallInst(CallInst&);

  std::tuple< Function*, std::vector<Value*> > extractExpression(Value* V);
};
}
