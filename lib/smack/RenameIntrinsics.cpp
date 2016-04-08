//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "remove-dead-defs"

#include "smack/SmackOptions.h"
#include "llvm/Support/Debug.h"
#include "smack/RenameIntrinsics.h"

#include <vector>
#include <map>

namespace smack {

using namespace llvm;

  bool RenameIntrinsics::runOnModule(Module& M) {
    
    std::map<std::string, Function*> FM;
    
    for (Module::iterator F = M.begin(); F != M.end(); ++F) {
      std::string name = F->getName();
      if (name == "foo1")
	FM["foo1"] = &(*F);
      else if (name == "foo2")
	FM["foo2"] = &(*F);
      else if (name == "foo3")
	FM["foo3"] = &(*F);
      else if (name == "foo4")
	FM["foo4"] = &(*F);
      if (name == "foo5")
	FM["foo5"] = &(*F);
      else if (name == "foo6")
	FM["foo6"] = &(*F);
      else if (name == "foo7")
	FM["foo7"] = &(*F);
      else if (name == "foo8")
	FM["foo8"] = &(*F);
    }
    
    if(FM.size()) {
      for (Module::iterator func = M.begin(); func != M.end(); ++func) {
        for (auto I = inst_begin(func); I != inst_end(func); ++I) {
          if(CallInst* callinst = dyn_cast<CallInst>(&*I)) {
            if(callinst->getCalledFunction()->getName() == "llvm.smul.with.overflow.i32") {
              callinst->setCalledFunction(FM["foo1"]);
            }
            else if(callinst->getCalledFunction()->getName() == "llvm.umul.with.overflow.i32") {
              callinst->setCalledFunction(FM["foo2"]);
            }
            else if(callinst->getCalledFunction()->getName() == "llvm.sadd.with.overflow.i32") {
              callinst->setCalledFunction(FM["foo3"]);
            }
            else if(callinst->getCalledFunction()->getName() == "llvm.uadd.with.overflow.i32") {
              callinst->setCalledFunction(FM["foo4"]);
            }
            else if(callinst->getCalledFunction()->getName() == "llvm.smul.with.overflow.i64") {
              callinst->setCalledFunction(FM["foo5"]);
            }
            else if(callinst->getCalledFunction()->getName() == "llvm.umul.with.overflow.i64") {
              callinst->setCalledFunction(FM["foo6"]);
            }
            else if(callinst->getCalledFunction()->getName() == "llvm.sadd.with.overflow.i64") {
              callinst->setCalledFunction(FM["foo7"]);
            }
            else if(callinst->getCalledFunction()->getName() == "llvm.uadd.with.overflow.i64") {
              callinst->setCalledFunction(FM["foo8"]);
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
