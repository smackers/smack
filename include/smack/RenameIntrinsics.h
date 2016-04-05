//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/User.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"


namespace smack {

class RenameIntrinsics : public llvm::ModulePass {
public:
  static char ID;
  RenameIntrinsics() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module& M);
};
}
