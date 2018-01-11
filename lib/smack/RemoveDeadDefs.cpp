//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "remove-dead-defs"

#include "smack/SmackOptions.h"
#include "smack/RemoveDeadDefs.h"
#include "smack/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/DataLayout.h"

#include <vector>

namespace smack {

using namespace llvm;

bool RemoveDeadDefs::runOnModule(Module& M) {
  TD = &M.getDataLayout();
  std::vector<Function*> dead;

  do {
    dead.clear();
    for (Function &F : M) {
      std::string name = F.getName();

      if (!(F.isDefTriviallyDead() || F.getNumUses() == 0))
        continue;

      if (name.find("__SMACK_") != std::string::npos)
        continue;

      if (name.find("__VERIFIER_assume") != std::string::npos)
	continue;

      if (SmackOptions::isEntryPoint(name))
        continue;

      DEBUG(errs() << "removing dead definition: " << name << "\n");
      dead.push_back(&F);
    }

    for (auto F : dead)
      F->eraseFromParent();
  } while (!dead.empty());

  return true;
}

// Pass ID variable
char RemoveDeadDefs::ID = 0;

// Register the pass
static RegisterPass<RemoveDeadDefs>
X("remove-dead-defs", "Remove Dead Definitions");

}
