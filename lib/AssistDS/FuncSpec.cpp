//===-- FuncSpec.cpp - Clone Functions With Constant Function Ptr Args ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass clones functions that take constant function pointers as arguments
// from some call sites. It changes those call sites to call cloned functions.
// 
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "funcspec"

#include "assistDS/FuncSpec.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"

#include <set>
#include <map>
#include <vector>

using namespace llvm;

// Pass statistics
STATISTIC(numCloned, "Number of Functions Cloned in FuncSpec");
STATISTIC(numReplaced, "Number of Calls Replaced");
//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM pass. Search for call sites, that take functions as arguments
//  Clone those functions, and pass the clone.
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
bool FuncSpec::runOnModule(Module& M) {
  std::map<CallInst*, std::vector<std::pair<unsigned, Constant*> > > cloneSites;
  std::map<std::pair<Function*, std::vector<std::pair<unsigned, Constant*> > >, Function* > toClone;

  for (Module::iterator I = M.begin(); I != M.end(); ++I)
    if (!I->isDeclaration() && !I->mayBeOverridden()) {
      std::vector<unsigned> FPArgs;
      for (Function::arg_iterator ii = I->arg_begin(), ee = I->arg_end();
           ii != ee; ++ii) {
        // check if this function has a FunctionType(or a pointer to) argument 
        if (const PointerType* Ty = dyn_cast<PointerType>(ii->getType())) {
          if (isa<FunctionType>(Ty->getElementType())) {
            // Store the index of such an argument
            FPArgs.push_back(ii->getArgNo());
            DEBUG(errs() << "Eligible: " << I->getName().str() << "\n");
          }
        } else if (isa<FunctionType>(ii->getType())) {
          // Store the index of such an argument
          FPArgs.push_back(ii->getArgNo());
          DEBUG(errs() << "Eligible: " << I->getName().str() << "\n");
        } 
      }
      // Now find all call sites that it is called from
      for(Value::user_iterator ui = I->user_begin(), ue = I->user_end();
          ui != ue; ++ui) {
        if (CallInst* CI = dyn_cast<CallInst>(*ui)) {
          // Check that it is the called value (and not an argument)
          if(CI->getCalledValue()->stripPointerCasts() == I) {
            std::vector<std::pair<unsigned, Constant*> > Consts;
            for (unsigned x = 0; x < FPArgs.size(); ++x)
              if (Constant* C = dyn_cast<Constant>(ui->getOperand(FPArgs.at(x) + 1))) {
                // If the argument passed, at any of the locations noted earlier
                // is a constant function, store the pair
                Consts.push_back(std::make_pair(FPArgs.at(x), C));
              }
            if (!Consts.empty()) {
              // If at least one of the arguments is a constant function,
              // we must clone the function.
              cloneSites[CI] = Consts;
              toClone[std::make_pair(I, Consts)] = 0;
            }
          }
        }
      }
    }

  numCloned += toClone.size();

  for (std::map<std::pair<Function*, std::vector<std::pair<unsigned, Constant*> > >, Function* >::iterator I = toClone.begin(), E = toClone.end(); I != E; ++I) {
    // Clone all the functions we need cloned
    ValueToValueMapTy VMap;
    Function* DirectF = CloneFunction(I->first.first, VMap, false);
    DirectF->setName(I->first.first->getName().str() + "_SPEC");
    DirectF->setLinkage(GlobalValue::InternalLinkage);
    I->first.first->getParent()->getFunctionList().push_back(DirectF);
    I->second = DirectF;
  }

  for (std::map<CallInst*, std::vector<std::pair<unsigned, Constant*> > >::iterator ii = cloneSites.begin(), ee = cloneSites.end(); ii != ee; ++ii) {
    // Transform the call sites, to call the clones
    Function *OldCallee = cast<Function>(ii->first->getCalledValue());
    Function *NewCallee = toClone[std::make_pair(OldCallee, ii->second)];
    ii->first->setCalledFunction(NewCallee);
    ++numReplaced;
  }

  return true;
}

// Pass ID variable
char FuncSpec::ID = 0;

// Register the pass
static RegisterPass<FuncSpec>
X("funcspec", "Specialize for Function Pointers");
