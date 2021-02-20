//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef RUSTFIXES_H
#define RUSTFIXES_H

#include "llvm/Pass.h"

namespace smack {

class RustFixes : public llvm::FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  RustFixes() : llvm::FunctionPass(ID) {}
  virtual llvm::StringRef getPassName() const;
  virtual bool runOnFunction(llvm::Function &F);
};
} // namespace smack

#endif // RUSTFIXES_H
