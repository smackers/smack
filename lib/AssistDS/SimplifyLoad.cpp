//===--------------- SimplifyLoad.cpp - Simplify load insts ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
// Derived from InstCombine
//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "simplifyload"

#include "assistDS/SimplifyLoad.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/DataLayout.h"

#include <set>
#include <map>
#include <vector>

using namespace llvm;

// Pass statistic
STATISTIC(numErased, "Number of Instructions Deleted");

//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM pass. Search for insert/extractvalue instructions
//  that can be simplified.
//
// Inputs:
//  M - A reference to the LLVM module to transform.
//
// Outputs:
//  M - The transformed LLVM module.
//
// Return value:
// true  - The module was modified.
// false - The module was not modified.
//
bool SimplifyLoad::runOnModule(Module& M) {
  // Repeat till no change
  bool changed;
  do {
    changed = false;
    for (Module::iterator F = M.begin(); F != M.end(); ++F) {
      for (Function::iterator B = F->begin(), FE = F->end(); B != FE; ++B) {      
        for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;) {
          LoadInst *LI = dyn_cast<LoadInst>(I++);
          if(!LI)
            continue;
          if(LI->hasOneUse()) {
            if(CastInst *CI = dyn_cast<CastInst>(*(LI->use_begin()))) {
              if(LI->getType()->isPointerTy()) {
                if(ConstantExpr *CE = dyn_cast<ConstantExpr>(LI->getOperand(0))) {
                  if(const PointerType *PTy = dyn_cast<PointerType>(CE->getOperand(0)->getType()))
                    if(PTy->getElementType() == CI->getType()) {
                      LoadInst *LINew = new LoadInst(CE->getOperand(0), "", LI);
                      CI->replaceAllUsesWith(LINew);
                    }
                }
              }
            }
          }


        }
      }
    }
  } while(changed);
  return (numErased > 0);
}

// Pass ID variable
char SimplifyLoad::ID = 0;

// Register the pass
static RegisterPass<SimplifyLoad>
X("simplify-load", "Simplify load insts");
