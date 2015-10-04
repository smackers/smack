//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "remove-dead-defs"

#include "smack/SmackOptions.h"
#include "smack/RemoveDeadDefs.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DataLayout.h"

#include <vector>

namespace smack {

using namespace llvm;

bool RemoveDeadDefs::runOnModule(Module& M) {
  TD = &getAnalysis<DataLayoutPass>().getDataLayout();
  std::vector<Function*> dead;

  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    std::string name = F->getName();

    if (!F->isDefTriviallyDead())
      continue;

    if (name.find("__SMACK_") != std::string::npos)
      continue;

    if (SmackOptions::isEntryPoint(name))
      continue;

    DEBUG(errs() << "removing dead definition: " << name << "\n");
    dead.push_back(F);
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

}
