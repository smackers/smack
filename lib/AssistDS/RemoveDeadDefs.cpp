//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "remove-dead-defs"

#include "assistDS/RemoveDeadDefs.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DataLayout.h"

#include <vector>

using namespace llvm;

bool RemoveDeadDefs::runOnModule(Module& M) {
  TD = &getAnalysis<DataLayoutPass>().getDataLayout();
  std::vector<Function*> dead;

  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    std::string name = F->getName();

    if (F->isDefTriviallyDead()
        && name.find("__SMACK_") == std::string::npos
        && name.find("main") == std::string::npos) {
      // TODO better way to know whether this is a top-level function.

      DEBUG(errs() << "removing dead definition: " << name << "\n");
      dead.push_back(F);
    }
  }

  for (auto F : dead)
    F->eraseFromParent();

  return true;
}

// Pass ID variable
char RemoveDeadDefs::ID = 0;

// Register the pass
static RegisterPass<RemoveDeadDefs>
X("remove-dead-defs", "Remove Dead Definitions");
