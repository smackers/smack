//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/SmackOptions.h"
#include "llvm/Support/CommandLine.h"

namespace smack {

const llvm::cl::opt<bool> SmackOptions::MemoryModelDebug(
  "mem-mod-dbg", llvm::cl::desc("Enable memory model debugging.")
);

const llvm::cl::opt<bool> SmackOptions::MemoryModelImpls(
  "mem-mod-impls", llvm::cl::desc("Provide implementations for memory model procedures.")
);

const llvm::cl::opt<bool> SmackOptions::SourceLocSymbols(
  "source-loc-syms", llvm::cl::desc("Include source locations in generated code.")
);

const llvm::cl::opt<bool> SmackOptions::BitPrecise(
  "bit-precise", llvm::cl::desc("Model non-pointer values as bit vectors.")
);

const llvm::cl::opt<bool> SmackOptions::BitPrecisePointers(
  "bit-precise-pointers", llvm::cl::desc("Model pointers as bit vectors.")
);

const llvm::cl::opt<bool> SmackOptions::NoMemoryRegionSplitting(
  "no-memory-splitting", llvm::cl::desc("Disable splitting memory into regions.")
);

const llvm::cl::opt<bool> SmackOptions::NoByteAccessInference(
  "no-byte-access-inference", llvm::cl::desc("Optimize bit-precision with DSA.")
);
}
