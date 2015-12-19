//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/MemoryAllocationChecker.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"

namespace smack {
using namespace llvm;
  bool MemoryAllocationChecker::runOnModule(Module& m) {
    std::cout << "in memory allocation checker\n";
    for (auto& F : m) {
      for (auto& B : F) {
        for (auto& I : B) {
          if(LoadInst* li = dyn_cast<LoadInst>(&I)) {
            errs() << li;
          } else if (StoreInst* si = dyn_cast<StoreInst>(&I)) {
            errs() << si;
          }
        }
      }
    }
    return false;
  }

  // Pass ID variable
  char MemoryAllocationChecker::ID = 0;
  static RegisterPass<MemoryAllocationChecker> MemoryAllocationCheckerPass("memory-allocation-checker", "SMACK Memory Allocation Checker");
}
