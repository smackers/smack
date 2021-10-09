//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/SimplifyLibCalls.h"

namespace smack {

using namespace llvm;

class SimplifyLibCalls : public FunctionPass,
                         public InstVisitor<SimplifyLibCalls> {
private:
  bool modified;
  LibCallSimplifier *simplifier;

public:
  static char ID;
  SimplifyLibCalls() : FunctionPass(ID) {}
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
  virtual bool runOnFunction(Function &F) override;
  void visitCallInst(CallInst &);
};
} // namespace smack
