//===-- SimplifyExtractValue.cpp - Remove extraneous extractvalue insts----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Simplify extractvalue
//
// Derived from InstCombine
//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "simplifyev"

#include "assistDS/SimplifyExtractValue.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/ArrayRef.h"
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
bool SimplifyEV::runOnModule(Module& M) {
  // Repeat till no change
  bool changed;
  do {
    changed = false;
    for (Module::iterator F = M.begin(); F != M.end(); ++F) {
      for (Function::iterator B = F->begin(), FE = F->end(); B != FE; ++B) {      
        for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;) {
          ExtractValueInst *EV = dyn_cast<ExtractValueInst>(I++);
          if(!EV)
            continue;
          Value *Agg = EV->getAggregateOperand();
          if (!EV->hasIndices()) {
            EV->replaceAllUsesWith(Agg);
            DEBUG(errs() << "EV:");
            DEBUG(errs() << "ERASE:");
            DEBUG(EV->dump());
            EV->eraseFromParent();
            numErased++;
            changed = true;
            continue;
          }
          if (Constant *C = dyn_cast<Constant>(Agg)) {
            if (isa<UndefValue>(C)) {
              EV->replaceAllUsesWith(UndefValue::get(EV->getType()));
              DEBUG(errs() << "EV:");
              DEBUG(errs() << "ERASE:");
              DEBUG(EV->dump());
              EV->eraseFromParent();
              numErased++;
              changed = true;
              continue;
            }
            if (isa<ConstantAggregateZero>(C)) {
              EV->replaceAllUsesWith(Constant::getNullValue(EV->getType()));
              DEBUG(errs() << "EV:");
              DEBUG(errs() << "ERASE:");
              DEBUG(EV->dump());
              EV->eraseFromParent();
              numErased++;
              changed = true;
              continue;
            }
            if (isa<ConstantArray>(C) || isa<ConstantStruct>(C)) {
              // Extract the element indexed by the first index out of the constant
              Value *V = C->getOperand(*EV->idx_begin());
              if (EV->getNumIndices() > 1) {
                // Extract the remaining indices out of the constant indexed by the
                // first index
                ExtractValueInst *EV_new = ExtractValueInst::Create(V, 
                                                                    EV->getIndices().slice(1), 
                                                                    "", EV);
                EV->replaceAllUsesWith(EV_new);
                DEBUG(errs() << "EV:");
                DEBUG(errs() << "ERASE:");
                DEBUG(EV->dump());
                EV->eraseFromParent();
                numErased++;
                changed = true;
                continue;
              }  else {
                EV->replaceAllUsesWith(V);
                DEBUG(errs() << "EV:");
                DEBUG(errs() << "ERASE:");
                DEBUG(EV->dump());
                EV->eraseFromParent();
                numErased++;
                changed = true;
                continue;
              }
            }
            continue;
          }
          if (LoadInst * LI = dyn_cast<LoadInst>(Agg)) {
            // if the Agg value came from a load instruction
            // replace the extract value intruction with
            // a gep and a load.
            SmallVector<Value*, 8> Indices;
            Type *Int32Ty = Type::getInt32Ty(M.getContext());
            Indices.push_back(Constant::getNullValue(Int32Ty));
            for (ExtractValueInst::idx_iterator I = EV->idx_begin(), E = EV->idx_end();
                 I != E; ++I) {
              Indices.push_back(ConstantInt::get(Int32Ty, *I));
            }

            GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(LI->getOperand(0), Indices,
                                                                       LI->getName(), LI) ;
            LoadInst *LINew = new LoadInst(GEP, "", LI);
            EV->replaceAllUsesWith(LINew);
            EV->eraseFromParent();
            changed = true;
            numErased++;
            continue;
          }
          if (InsertValueInst *IV = dyn_cast<InsertValueInst>(Agg)) {
            bool done = false;
            // We're extracting from an insertvalue instruction, compare the indices
            const unsigned *exti, *exte, *insi, *inse;
            for (exti = EV->idx_begin(), insi = IV->idx_begin(),
                 exte = EV->idx_end(), inse = IV->idx_end();
                 exti != exte && insi != inse;
                 ++exti, ++insi) {
              if (*insi != *exti) {
                // The insert and extract both reference distinctly different elements.
                // This means the extract is not influenced by the insert, and we can
                // replace the aggregate operand of the extract with the aggregate
                // operand of the insert. i.e., replace
                // %I = insertvalue { i32, { i32 } } %A, { i32 } { i32 42 }, 1
                // %E = extractvalue { i32, { i32 } } %I, 0
                // with
                // %E = extractvalue { i32, { i32 } } %A, 0
                ExtractValueInst *EV_new = ExtractValueInst::Create(IV->getAggregateOperand(),
                                                                    EV->getIndices(), "", EV);
                EV->replaceAllUsesWith(EV_new);
                DEBUG(errs() << "EV:");
                DEBUG(errs() << "ERASE:");
                DEBUG(EV->dump());
                EV->eraseFromParent();
                numErased++;
                done = true;
                changed = true;
                break;
              }
            }
            if(done)
              continue;
            if (exti == exte && insi == inse) {
              // Both iterators are at the end: Index lists are identical. Replace
              // %B = insertvalue { i32, { i32 } } %A, i32 42, 1, 0
              // %C = extractvalue { i32, { i32 } } %B, 1, 0
              // with "i32 42"
              EV->replaceAllUsesWith(IV->getInsertedValueOperand());
              DEBUG(errs() << "EV:");
              DEBUG(errs() << "ERASE:");
              DEBUG(EV->dump());
              EV->eraseFromParent();
              numErased++;
              changed = true;
              continue;
            }
            if (exti == exte) {
              // The extract list is a prefix of the insert list. i.e. replace
              // %I = insertvalue { i32, { i32 } } %A, i32 42, 1, 0
              // %E = extractvalue { i32, { i32 } } %I, 1
              // with
              // %X = extractvalue { i32, { i32 } } %A, 1
              // %E = insertvalue { i32 } %X, i32 42, 0
              // by switching the order of the insert and extract (though the
              // insertvalue should be left in, since it may have other uses).
              Value *NewEV = ExtractValueInst::Create(IV->getAggregateOperand(),
                                                      EV->getIndices(), "", EV);
              Value *NewIV = InsertValueInst::Create(NewEV, IV->getInsertedValueOperand(),
                                                     makeArrayRef(insi, inse), "", EV);
              EV->replaceAllUsesWith(NewIV);
              DEBUG(errs() << "EV:");
              DEBUG(errs() << "ERASE:");
              DEBUG(EV->dump());
              EV->eraseFromParent();
              numErased++;
              changed = true;
              continue;
            }
            if (insi == inse) {
              // The insert list is a prefix of the extract list
              // We can simply remove the common indices from the extract and make it
              // operate on the inserted value instead of the insertvalue result.
              // i.e., replace
              // %I = insertvalue { i32, { i32 } } %A, { i32 } { i32 42 }, 1
              // %E = extractvalue { i32, { i32 } } %I, 1, 0
              // with
              // %E extractvalue { i32 } { i32 42 }, 0
              ExtractValueInst *EV_new = ExtractValueInst::Create(IV->getInsertedValueOperand(),
                                                                  makeArrayRef(exti, exte), "", EV);
              EV->replaceAllUsesWith(EV_new);
              DEBUG(errs() << "EV:");
              DEBUG(errs() << "ERASE:");
              DEBUG(EV->dump());
              EV->eraseFromParent();
              numErased++;
              changed = true;
              continue;
            }
          }
        }
      }
    }
  } while(changed);
  return (numErased > 0);
}

// Pass ID variable
char SimplifyEV::ID = 0;

// Register the pass
static RegisterPass<SimplifyEV>
X("simplify-ev", "Simplify extract/insert value insts");
