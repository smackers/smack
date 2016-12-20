//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "remove-dead-defs"

#include "smack/SmackOptions.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Regex.h"
#include "llvm/ADT/SmallVector.h"

#include "smack/RenameIntrinsics.h"

#include <vector>
#include <map>
#include <iostream>

namespace smack {

  using namespace llvm;

  bool RenameIntrinsics::runOnModule(Module& M) {
    StringRef arithStrRef("llvm\\.(s|u)(mul|add|sub|div)\\.with\\.overflow\\.i(8|16|32|64)");
    Regex arithRegex(arithStrRef);

    for (auto& func : M) {
      for (auto I = inst_begin(func); I != inst_end(func); ++I) {
	if (CallInst* callinst = dyn_cast<CallInst>(&*I)) {
	  StringRef functionName(callinst->getCalledFunction()->getName());
	  SmallVector<StringRef, 1> matches;
	  if (arithRegex.match(functionName, &matches) && matches.size() > 0) {
	    StringRef replacementFuncName("smack." + std::string(matches[0]));
	    auto replacementFunc = M.getNamedValue(replacementFuncName);
	    if (replacementFunc) {
	      callinst->setCalledFunction(replacementFunc);
	    } else {
	      return false;
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
