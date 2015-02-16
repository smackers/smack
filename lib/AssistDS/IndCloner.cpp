//===-- IndCloner.cpp - Clone Indirectly Called Functions -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass clones functions which can be called indirectly and then updates
// direct calls to call the clone.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "indclone"

#include "assistDS/IndCloner.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"

#include <vector>

using namespace llvm;

// Pass ID variable
char IndClone::ID = 0;

// Register the Indirect Function Cloner Pass
static RegisterPass<IndClone>
X("indclone", "Indirect call cloning");

// Pass statistics
STATISTIC(numCloned,   "Number of Functions Cloned in IndCloner");
STATISTIC(numReplaced, "Number of Calls Replaced");

//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM pass.  Search for functions which could be called
//  indirectly and create clones for them which are only called by direct
//  calls.
//
// Inputs:
//  M - A reference to the LLVM module to transform.
//
// Outputs:
//  M - The transformed LLVM module.
//
// Return value:
//  true  - The module was modified.
//  false - The module was not modified.
//
bool
IndClone::runOnModule(Module& M) {
  // Set of functions to clone
  std::vector<Function*> toClone;

  //
  // Check all of the functions in the module.  If the function could be called
  // by an indirect function call, add it to our worklist of functions to
  // clone.
  //
  for (Module::iterator I = M.begin(); I != M.end(); ++I) {
    // Flag whether the function should be cloned
    bool pleaseCloneTheFunction = false;

    //
    // Only clone functions which are defined and cannot be replaced by another
    // function by the linker.
    //
    if (!I->isDeclaration() && !I->mayBeOverridden()) {
      for (Value::user_iterator ui = I->user_begin(), ue = I->user_end();
          ui != ue; ++ui) {
        if (!isa<CallInst>(*ui) && !isa<InvokeInst>(*ui)) {
          if(!ui->use_empty())
          //
          // If this function is used for anything other than a direct function
          // call, then we want to clone it.
          //
          pleaseCloneTheFunction = true;
        } else {
          //
          // This is a call instruction, but hold up ranger!  We need to make
          // sure that the function isn't passed as an argument to *another*
          // function.  That would make the function usable in an indirect
          // function call.
          //
          for (unsigned index = 1; index < ui->getNumOperands(); ++index) {
            if (ui->getOperand(index)->stripPointerCasts() == I) {
              pleaseCloneTheFunction = true;
              break;
            }
          }
        }

        //
        // If we've discovered that the function could be used by an indirect
        // call site, schedule it for cloning.
        //
        if (pleaseCloneTheFunction) {
          toClone.push_back(I);
          break;
        }
      }
    }
  }

  //
  // Update the statistics on the number of functions we'll be cloning.
  // We only update the statistic if we want to clone one or more functions;
  // due to the magic of how statistics work, avoiding assignment prevents it
  // from needlessly showing up.
  //
  if (toClone.size())
    numCloned += toClone.size();

  //
  // Go through the worklist and clone each function.  After cloning a
  // function, change all direct calls to use the clone instead of using the
  // original function.
  //
  for (unsigned index = 0; index < toClone.size(); ++index) {
    //
    // Clone the function and give it a name indicating that it is a clone to
    // be used for direct function calls.
    //
    Function * Original = toClone[index];
    ValueToValueMapTy VMap;
    Function* DirectF = CloneFunction(Original, VMap, false);
    DirectF->setName(Original->getName() + "_DIRECT");

    //
    // Make the clone internal; external code can use the original function.
    //
    DirectF->setLinkage(GlobalValue::InternalLinkage);

    //
    // Link the cloned function into the set of functions belonging to the
    // module.
    //
    Original->getParent()->getFunctionList().push_back(DirectF);

    //
    // Find all uses of the function that use it as a direct call.  Change
    // them to use the clone.
    //
    for (Value::user_iterator ui = Original->user_begin(),
                             ue = Original->user_end();
        ui != ue; ) {
      CallInst *CI = dyn_cast<CallInst>(*ui);
      ui++;
      if (CI) {
        if (CI->getCalledFunction() == Original) {
          ++numReplaced;
          CI->setCalledFunction(DirectF);
        }
      }
    }
  }
  
  //
  // Assume that we've cloned at least one function.
  //
  return true;
}

