//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/ADT/StringRef.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include <map>
#include <queue>
#include <string>

namespace smack {

using namespace llvm;

class VerifierCodeMetadata : public ModulePass,
                             public InstVisitor<VerifierCodeMetadata> {
private:
  std::queue<Instruction *> workList;
  std::map<const Function *, std::string> verifierPrimitives;

public:
  static char ID;
  VerifierCodeMetadata() : ModulePass(ID) {}
  virtual bool runOnModule(Module &M) override;
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
  void visitCallInst(CallInst &);
  void visitInstruction(Instruction &);
  static bool isMarked(const Instruction &I);
  static StringRef getVerifierPrimitive(const CallInst &I);
};
} // namespace smack
