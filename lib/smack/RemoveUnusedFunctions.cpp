//
// This file is distributed under the MIT License. See LICENSE for details.
//

//
// This pass removes functions from the IR not reachable from any entry point.
//

#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Module.h"

#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "smack/RemoveUnusedFunctions.h"

#include <set>
#include <iostream>

namespace smack {

using namespace llvm;

void getUsedFunctions(CallGraphNode *CGN, std::set<Function *> &used) {
  if (!CGN) { return; }

  Function *function = CGN->getFunction();
  if (used.count(function)) { return; }

  used.insert(CGN->getFunction());
  for (auto callee : *CGN) {
    if (std::get<0>(callee)) {
      getUsedFunctions(std::get<1>(callee), used);
    }
  }
}

bool RemoveUnusedFunctions::runOnModule(Module &m) {
  if (!SmackOptions::RemoveUnused) {
    return false;
  }
  std::set<Function *> allFunctions;
  std::set<Function *> entryFunctions;
  std::set<Function *> usedFunctions;
  CallGraph CG = CallGraph(m);

  for (auto F = m.begin(), FEnd = m.end(); F != FEnd; ++F) {
    if (F->isIntrinsic() || F->empty() ||
        (F->hasName() && Naming::isSmackName(F->getName()))) {
      continue;
    }

    allFunctions.insert(&*F);

    if (F->hasName() && SmackOptions::isEntryPoint(F->getName())) {
      entryFunctions.insert(&*F);
    }
  }

  for (auto E : entryFunctions) {
    auto entryCGN = CG[E];
    getUsedFunctions(entryCGN, usedFunctions);
  }

  for (auto F : allFunctions) {
    if (!usedFunctions.count(F)) {
      F->dropAllReferences();
    }
  }

  return true;
}

// Pass ID variable
char RemoveUnusedFunctions::ID = 0;

StringRef RemoveUnusedFunctions::getPassName() const { return "RemoveUnusedFunctions"; }
} // namespace smack
