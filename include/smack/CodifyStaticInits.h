//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace smack {

class CodifyStaticInits : public llvm::ModulePass {
private:
  const llvm::DataLayout *TD;

public:
  static char ID;

  CodifyStaticInits() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
};

llvm::Pass *createCodifyStaticInitsPass();

} // namespace smack
