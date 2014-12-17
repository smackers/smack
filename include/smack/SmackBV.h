//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKBV_H
#define SMACKBV_H

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"

using namespace std;
using llvm::errs;

namespace smack {

class SmackBV : public llvm::ModulePass {
private:
  static bool misBVRequired;
public:
  static char ID; // Pass identification, replacement for typeid

  SmackBV() : ModulePass(ID) {}
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const {
	AU.setPreservesAll();
  }

  bool isBVRequired();
  bool isBVPredicate(unsigned opcode);
  virtual bool runOnModule(llvm::Module& m);
};
}

#endif // SMACKBV_H

