//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef INSERTDUMMYMAIN_H
#define INSERTDUMMYMAIN_H

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include <map>

namespace smack {

class InsertDummyMain : public llvm::ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  InsertDummyMain() : llvm::ModulePass(ID) {}
  virtual llvm::StringRef getPassName() const;
  virtual bool runOnModule(llvm::Module &m);
};
} // namespace smack

#endif // INSERTDUMMYMAIN_H
