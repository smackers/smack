//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace smack {

using namespace llvm;

class ExtractContracts : public ModulePass, public InstVisitor<ExtractContracts> {
private:
  bool modified;
  bool hasDominatedIncomingValue(Value* V);
  std::tuple< Function*, std::vector<Value*> > extractExpression(Value* V);

public:
  static char ID;
  ExtractContracts() : ModulePass(ID) {}
  virtual bool runOnModule(Module& M);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<DominatorTreeWrapperPass>();
  }
  void visitCallInst(CallInst&);
};
}
