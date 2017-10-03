//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/SmackOptions.h"
#include "llvm/Support/CommandLine.h"

namespace smack {

const llvm::cl::list<std::string> SmackOptions::EntryPoints(
  "entry-points",
  llvm::cl::ZeroOrMore,
  llvm::cl::desc("Entry point procedure names"),
  llvm::cl::value_desc("PROCS")
);

const llvm::cl::opt<bool> SmackOptions::Warnings(
  "warnings", llvm::cl::desc("Enable warnings.")
);

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

const llvm::cl::opt<bool> SmackOptions::AddTiming("timing-annotations", llvm::cl::desc("Add timing annotations."));

const llvm::cl::opt<bool> SmackOptions::NoMemoryRegionSplitting(
  "no-memory-splitting", llvm::cl::desc("Disable splitting memory into regions.")
);

const llvm::cl::opt<bool> SmackOptions::NoByteAccessInference(
  "no-byte-access-inference", llvm::cl::desc("Optimize bit-precision with DSA.")
);

const llvm::cl::opt<bool> SmackOptions::FloatEnabled(
  "float", llvm::cl::desc("Enable interpreted floating-point type")
);

const llvm::cl::opt<bool> SmackOptions::MemorySafety(
  "memory-safety", llvm::cl::desc("Enable memory safety checks"));

bool SmackOptions::isEntryPoint(std::string name) {
  for (auto EP : EntryPoints)
    if (name == EP)
      return true;
  return false;
}

}
