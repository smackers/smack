//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef ANNOTATELOOPEXITS_H
#define ANNOTATELOOPEXITS_H

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include <map>

namespace llvm {
class LoopInfo;
}

namespace smack {

namespace detail {
// Shared body. The legacy wrapper caches `loopExitFn` in doInitialization;
// the NewPM wrapper has no init hook so it fetches the function per call.
bool runAnnotateLoopExits(llvm::Function &F, llvm::LoopInfo &LI,
                          llvm::Function *loopExitFn);
} // namespace detail

class AnnotateLoopExits : public llvm::FunctionPass {
private:
  llvm::Function *LoopExitFunction;

public:
  static char ID; // Pass identification, replacement for typeid
  AnnotateLoopExits() : llvm::FunctionPass(ID) {}
  bool doInitialization(llvm::Module &M) override;
  virtual llvm::StringRef getPassName() const override;
  virtual bool runOnFunction(llvm::Function &F) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage &) const override;
};

class AnnotateLoopExitsNewPM
    : public llvm::PassInfoMixin<AnnotateLoopExitsNewPM> {
public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &FAM);
  static llvm::StringRef name() { return "AnnotateLoopExitsNewPM"; }
};
} // namespace smack

#endif // ANNOTATELOOPEXITS_H
