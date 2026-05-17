//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
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

// NewPM sibling. Delegates to a stack-allocated legacy instance; the
// `workList` queue is per-instance state, freshly initialized each run.
class VerifierCodeMetadataNewPM
    : public PassInfoMixin<VerifierCodeMetadataNewPM> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &);
  static StringRef name() { return "VerifierCodeMetadataNewPM"; }
};
} // namespace smack
