//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {
class LoopInfo;
}

namespace smack {

using namespace llvm;

class ExtractContracts : public ModulePass {
public:
  static char ID;
  ExtractContracts() : ModulePass(ID) {}
  virtual bool runOnModule(Module &M) override;
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override;

  // Shared body. Caller supplies a per-function LoopInfo getter (legacy:
  // getAnalysis<LoopInfoWrapperPass>(F); NewPM: FAM.getResult<LoopAnalysis>(F))
  static bool
  runImpl(Module &M,
          llvm::function_ref<llvm::LoopInfo &(llvm::Function &)> getLoopInfo);
};

class ExtractContractsNewPM
    : public PassInfoMixin<ExtractContractsNewPM> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);
  static StringRef name() { return "ExtractContractsNewPM"; }
};
} // namespace smack
