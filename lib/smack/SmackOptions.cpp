//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "SmackOptions.h"
#include "SmackRepFactory.h"
#include "llvm/Support/CommandLine.h"

namespace smack {

// Enable memory model to be specified on the command line
const llvm::cl::opt<MemMod> SmackOptions::MemoryModel(
  "mem-mod", 
  llvm::cl::desc("Set the memory model:"),
  llvm::cl::values(
    clEnumVal(flat, "flat memory model"),
    clEnumVal(twodim, "two dimensional memory model"),
    clEnumValEnd));

const llvm::cl::opt<bool> SmackOptions::MemoryModelDebug(
  "mem-mod-dbg", llvm::cl::desc("Enable memory model debugging:")
);

const llvm::cl::opt<bool> SmackOptions::IgnoreMemoryModelAsserts(
  "no-mem-mod-asserts", llvm::cl::desc("Ignore memory model assertions:")
);

const llvm::cl::opt<bool> SmackOptions::MemoryModelImpls(
  "mem-mod-impls", llvm::cl::desc("Provide implementations for memory model procedures:")
);

}
