//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/SmackOptions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Regex.h"

namespace smack {

const llvm::cl::list<std::string>
    SmackOptions::EntryPoints("entry-points", llvm::cl::ZeroOrMore,
                              llvm::cl::desc("Entry point procedure names"),
                              llvm::cl::value_desc("PROCS"));

const llvm::cl::list<std::string> SmackOptions::CheckedFunctions(
    "checked-functions", llvm::cl::ZeroOrMore,
    llvm::cl::desc("Functions in which to check properties"),
    llvm::cl::value_desc("PROCS"));

const llvm::cl::opt<SmackWarnings::WarningLevel> SmackOptions::WarningLevel(
    "warn-type", llvm::cl::desc("Enable certain type of warning messages."),
    llvm::cl::values(
        clEnumValN(SmackWarnings::WarningLevel::Silent, "silent",
                   "No warning messages"),
        clEnumValN(SmackWarnings::WarningLevel::Approximate, "approximate",
                   "Enable warnings about introduced approximations"),
        clEnumValN(SmackWarnings::WarningLevel::Info, "info",
                   "Enable warnings about introduced approximations and "
                   "translation information")));

const llvm::cl::opt<bool> SmackOptions::ColoredWarnings(
    "colored-warnings", llvm::cl::desc("Enable colored warning messages."));

const llvm::cl::opt<bool> SmackOptions::MemoryModelDebug(
    "mem-mod-dbg", llvm::cl::desc("Enable memory model debugging."));

const llvm::cl::opt<bool> SmackOptions::MemoryModelImpls(
    "mem-mod-impls",
    llvm::cl::desc("Provide implementations for memory model procedures."));

const llvm::cl::opt<bool> SmackOptions::SourceLocSymbols(
    "source-loc-syms",
    llvm::cl::desc("Include source locations in generated code."));

llvm::cl::opt<bool> SmackOptions::BitPrecise(
    "bit-precise", llvm::cl::desc("Model integer values as bit-vectors."));

const llvm::cl::opt<bool> SmackOptions::BitPrecisePointers(
    "bit-precise-pointers",
    llvm::cl::desc("Model pointer values as bit-vectors."));

const llvm::cl::opt<bool>
    SmackOptions::AddTiming("timing-annotations",
                            llvm::cl::desc("Add timing annotations."));

const llvm::cl::opt<bool> SmackOptions::RewriteBitwiseOps(
    "rewrite-bitwise-ops",
    llvm::cl::desc(
        "Provides models for bitwise operations in integer encoding."));

const llvm::cl::opt<bool> SmackOptions::NoMemoryRegionSplitting(
    "no-memory-splitting",
    llvm::cl::desc("Disable splitting memory into regions."));

const llvm::cl::opt<bool> SmackOptions::NoByteAccessInference(
    "no-byte-access-inference",
    llvm::cl::desc("Optimize bit-precision with DSA."));

const llvm::cl::opt<bool> SmackOptions::FloatEnabled(
    "float", llvm::cl::desc("Enable interpreted floating-point type"));

const llvm::cl::opt<bool>
    SmackOptions::MemorySafety("memory-safety",
                               llvm::cl::desc("Enable memory safety checks"));

const llvm::cl::opt<bool> SmackOptions::IntegerOverflow(
    "integer-overflow", llvm::cl::desc("Enable integer overflow checks"));

const llvm::cl::opt<bool> SmackOptions::FailOnLoopExit(
    "fail-on-loop-exit",
    llvm::cl::desc("Add assert(false) to the end of each loop"));

const llvm::cl::opt<LLVMAssumeType> SmackOptions::LLVMAssumes(
    "llvm-assumes",
    llvm::cl::desc(
        "Optionally enable generation of Boogie assumes from LLVM assumes"),
    llvm::cl::values(clEnumValN(LLVMAssumeType::none, "none",
                                "disable generation of assume statements"),
                     clEnumValN(LLVMAssumeType::use, "use",
                                "enable generation of assume statements"),
                     clEnumValN(LLVMAssumeType::check, "check",
                                "enable checking of assume statements")));

const llvm::cl::opt<bool>
    SmackOptions::RustPanics("rust-panics",
                             llvm::cl::desc("Enable Rust panic checking"));

const llvm::cl::opt<bool> SmackOptions::WrappedIntegerEncoding(
    "wrapped-integer-encoding",
    llvm::cl::desc(
        "Enable wrapped integer arithmetic and signedness-aware comparison"));

bool SmackOptions::isEntryPoint(llvm::StringRef name) {
  for (auto EP : EntryPoints)
    if (name == EP)
      return true;
  return false;
}

bool SmackOptions::shouldCheckFunction(llvm::StringRef name) {
  if (CheckedFunctions.size() == 0) {
    return true;
  }
  for (llvm::StringRef s : CheckedFunctions) {
    llvm::SmallVector<llvm::StringRef, 10> matches;
    if (llvm::Regex(s).match(name, &matches) && matches[0] == name) {
      return true;
    }
  }
  return false;
}
} // namespace smack
