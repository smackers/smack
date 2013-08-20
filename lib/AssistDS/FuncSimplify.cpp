//===-------- FuncSimplify.cpp - Replace Global Aliases -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "func-simplify"

#include "assistDS/FuncSimplify.h"
#include "llvm/Attributes.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"

#include <set>
#include <map>
#include <vector>

using namespace llvm;

// Pass statistics
STATISTIC(numChanged,   "Number of aliases deleted");

//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM pass.
//  Replace all internal aliases with the
//  aliasee value
//
// Inputs:
//  M - A reference to the LLVM module to transform
//
// Outputs:
//  M - The transformed LLVM module.
//
// Return value:
//  true  - The module was modified.
//  false - The module was not modified.
//
bool FuncSimplify::runOnModule(Module& M) {

  std::vector<GlobalAlias*> toDelete;
  for (Module::alias_iterator I = M.alias_begin(); I != M.alias_end(); ++I) {
    if(!I->hasInternalLinkage())
      continue;
    I->replaceAllUsesWith(I->getAliasee());
    toDelete.push_back(I);
  }
  numChanged += toDelete.size();

  while(!toDelete.empty()) {
    GlobalAlias *I = toDelete.back();
    toDelete.pop_back();
    I->eraseFromParent();
  }


  return true;
}

// Pass ID variable
char FuncSimplify::ID = 0;

// Register the pass
static RegisterPass<FuncSimplify>
X("func-simplify", "Delete Aliases");
