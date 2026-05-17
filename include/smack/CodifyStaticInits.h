//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace smack {

class DSAWrapper;

class CodifyStaticInits : public llvm::ModulePass {
private:
  const llvm::DataLayout *TD;

public:
  static char ID;

  CodifyStaticInits() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M) override;
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

  // Shared body for legacy + NewPM. Caller supplies the DSAWrapper.
  static bool runImpl(llvm::Module &M, DSAWrapper &dsa);
};

class CodifyStaticInitsNewPM
    : public llvm::PassInfoMixin<CodifyStaticInitsNewPM> {
public:
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
  static llvm::StringRef name() { return "CodifyStaticInitsNewPM"; }
};

llvm::Pass *createCodifyStaticInitsPass();

} // namespace smack
