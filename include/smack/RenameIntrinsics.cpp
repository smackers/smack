
//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "remove-dead-defs"

#include "smack/SmackOptions.h"
#include "llvm/Support/Debug.h"
#include "smack/RenameIntrinsics.h"

#include <vector>

namespace smack {

  using namespace llvm;

  bool RenameIntrinsics::runOnModule(Module& M) {

    Function *foo = NULL;

    for (Module::iterator F = M.begin(); F != M.end(); ++F) {
      std::string name = F->getName();
      if (name == "foo")
	foo = &(*F);
    }

    if(foo) {
      for (Module::iterator func = M.begin(); func != M.end(); ++func) {
        for (inst_iterator I = inst_begin(func); I != inst_end(func); ++I) {
          if(auto callinst = dyn_cast<CallInst>(&*I)) {
            if(callinst->getCalledFunction()->getName() == "llvm.smul.with.overflow.i32") {
              callinst->setCalledFunction(foo);
            }
          }
        }
      }
    }

    return true;
  }

  // Pass ID variable
  char RenameIntrinsics::ID = 0;

  // Register the pass
  static RegisterPass<RenameIntrinsics>
  X("rename-intrinsics", "Rename LLVM Intrinsics");

}
