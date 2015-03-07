//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef SMACKOPTIONS_H
#define SMACKOPTIONS_H

#include "llvm/Support/CommandLine.h"

namespace smack {
class SmackOptions {
public:
  static const llvm::cl::opt<bool> MemoryModelDebug;
  static const llvm::cl::opt<bool> MemoryModelImpls;
  
  static const llvm::cl::opt<bool> SourceLocSymbols;
  static const llvm::cl::opt<bool> BitPrecise;
  static const llvm::cl::opt<bool> NoByteAccessInference;
};
}

#endif // SMACKREP_H
