//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace smack {

namespace detail {
bool runRemoveDeadDefs(llvm::Module &M);
} // namespace detail

class RemoveDeadDefs : public llvm::ModulePass {
private:
  const llvm::DataLayout *TD;

public:
  static char ID;
  RemoveDeadDefs() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M) override;
};

class RemoveDeadDefsNewPM : public llvm::PassInfoMixin<RemoveDeadDefsNewPM> {
public:
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
  static llvm::StringRef name() { return "RemoveDeadDefsNewPM"; }
};
} // namespace smack
