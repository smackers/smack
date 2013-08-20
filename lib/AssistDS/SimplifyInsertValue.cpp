//===-- SimplifyInsertValue.cpp - Remove extraneous insertvalue insts------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Simplify insertvalue
// Replace insertvalue by storess where possible
//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "simplify-iv"

#include "assistDS/SimplifyInsertValue.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/PatternMatch.h"
#include "llvm/DataLayout.h"

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
//  Entry point for this LLVM pass. Search for insertvalue instructions
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
bool SimplifyIV::runOnModule(Module& M) {
  // Repeat till no change
  bool changed;
  do {
    changed = false;
    std::vector<StoreInst*> worklist;
    for (Module::iterator F = M.begin(); F != M.end(); ++F) {
      for (Function::iterator B = F->begin(), FE = F->end(); B != FE; ++B) {      
        for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;) {
          InsertValueInst *IV = dyn_cast<InsertValueInst>(I++);
          if(!IV)
            continue;
          // Find all insert value instructions.
          if(!IV->hasOneUse())
            continue;
          // Check that its only use is a StoreInst
          StoreInst *SI = dyn_cast<StoreInst>(*(IV->use_begin()));
          if(!SI)
            continue;
          // Check that it is the stored value
          if(SI->getOperand(0) != IV)
            continue;
          changed = true;
          numErased++;
          do {
            // replace by a series of gep/stores
            SmallVector<Value*, 8> Indices;
            Type *Int32Ty = Type::getInt32Ty(M.getContext());
            Indices.push_back(Constant::getNullValue(Int32Ty));
            for (InsertValueInst::idx_iterator I = IV->idx_begin(), E = IV->idx_end();
                 I != E; ++I) {
              Indices.push_back(ConstantInt::get(Int32Ty, *I));
            }
            GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(SI->getOperand(1), Indices,
                                                                       SI->getName(), SI) ;
            new StoreInst(IV->getInsertedValueOperand(), GEP, SI);
            IV = dyn_cast<InsertValueInst>(IV->getAggregateOperand());

          } while(IV);
          worklist.push_back(SI);
        }
      }
    }
    while(!worklist.empty()) {
      StoreInst *SI = worklist.back();
      worklist.pop_back();
      SI->eraseFromParent();
    }
  } while(changed);
  return (numErased > 0);
}

// Pass ID variable
char SimplifyIV::ID = 0;

// Register the pass
static RegisterPass<SimplifyIV>
X("simplify-iv", "Simplify insert value");
