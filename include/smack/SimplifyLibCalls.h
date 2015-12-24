//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/SimplifyLibCalls.h"

namespace smack {

using namespace llvm;

class SimplifyLibCalls : public ModulePass, public InstVisitor<SimplifyLibCalls> {
private:
  bool modified;
  LibCallSimplifier* simplifier;
public:
  static char ID;
  SimplifyLibCalls() : ModulePass(ID) {}
  virtual void getAnalysisUsage(AnalysisUsage& AU) const;
  virtual bool runOnModule(Module& M);
  void visitCallInst(CallInst&);
};
}
