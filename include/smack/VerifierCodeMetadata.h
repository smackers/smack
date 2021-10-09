//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include <queue>

namespace smack {

using namespace llvm;

class VerifierCodeMetadata : public ModulePass,
                             public InstVisitor<VerifierCodeMetadata> {
private:
  std::queue<Instruction *> workList;

public:
  static char ID;
  VerifierCodeMetadata() : ModulePass(ID) {}
  virtual bool runOnModule(Module &M) override;
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
  void visitCallInst(CallInst &);
  void visitInstruction(Instruction &);
  static bool isMarked(const Instruction &I);
};
} // namespace smack
