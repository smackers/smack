//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef SMACKOPTIONS_H
#define SMACKOPTIONS_H

#include "llvm/Support/CommandLine.h"

#include "smack/SmackWarnings.h"

namespace smack {
class SmackOptions {
public:
  static const llvm::cl::list<std::string> EntryPoints;

  static const llvm::cl::opt<SmackWarnings::WarningLevel> WarningLevel;
  static const llvm::cl::opt<bool> ColoredWarnings;

  static const llvm::cl::opt<bool> MemoryModelDebug;
  static const llvm::cl::opt<bool> MemoryModelImpls;

  static const llvm::cl::opt<bool> SourceLocSymbols;
  static llvm::cl::opt<bool> BitPrecise;
  static const llvm::cl::opt<bool> BitPrecisePointers;
  static const llvm::cl::opt<bool> NoMemoryRegionSplitting;
  static const llvm::cl::opt<bool> NoByteAccessInference;
  static const llvm::cl::opt<bool> FloatEnabled;
  static const llvm::cl::opt<bool> MemorySafety;
  static const llvm::cl::opt<bool> IntegerOverflow;
  static const llvm::cl::opt<bool> AddTiming;

  static bool isEntryPoint(std::string);
};
}

#endif // SMACKREP_H
