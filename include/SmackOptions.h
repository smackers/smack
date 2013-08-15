//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef SMACKOPTIONS_H
#define SMACKOPTIONS_H

#include "llvm/Support/CommandLine.h"

namespace smack {
  enum MemMod {
    flat, twodim
  };
  
class SmackOptions {
public:
  static const llvm::cl::opt<MemMod> MemoryModel;
  static const llvm::cl::opt<bool> MemoryModelDebug;
  static const llvm::cl::opt<bool> IgnoreMemoryModelAsserts;
  static const llvm::cl::opt<bool> MemoryModelImpls;
  
  static const llvm::cl::opt<bool> SourceLocSymbols;
};
}

#endif // SMACKREP_H
