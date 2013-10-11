//===-- AllocatorIdentification.cpp - Identify wrappers to allocators -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
// A pass to identify functions that act as wrappers to malloc and other 
// allocators.
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "allocator-identify"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"

#include <set>
#include <map>
#include <vector>
#include <string>

#include "dsa/AllocatorIdentification.h"

using namespace llvm;

STATISTIC(numAllocators, "Number of malloc-like allocators");
STATISTIC(numDeallocators, "Number of free-like deallocators");

bool AllocIdentify::flowsFrom(Value *Dest,Value *Src) {
  if(Dest == Src)
    return true;
  if(ReturnInst *Ret = dyn_cast<ReturnInst>(Dest)) {
    return flowsFrom(Ret->getReturnValue(), Src);
  }
  if(PHINode *PN = dyn_cast<PHINode>(Dest)) {
    Function *F = PN->getParent()->getParent();
    LoopInfo &LI = getAnalysis<LoopInfo>(*F);
    // If this is a loop phi, ignore.
    if(LI.isLoopHeader(PN->getParent()))
      return false;
    bool ret = true;
    for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
      ret = ret && flowsFrom(PN->getIncomingValue(i), Src);
    }
    return ret;
  }
  if(BitCastInst *BI = dyn_cast<BitCastInst>(Dest)) {
    return flowsFrom(BI->getOperand(0), Src);
  }
  if(isa<ConstantPointerNull>(Dest))
    return true;
  return false;
}

bool isNotStored(Value *V) {
  // check that V is not stored to a location that is accessible outside this fn
  for(Value::use_iterator ui = V->use_begin(), ue = V->use_end();
      ui != ue; ++ui) {
    if(isa<StoreInst>(*ui))
      return false;
    if(isa<ICmpInst>(*ui))
      continue;
    if(isa<ReturnInst>(*ui))
      continue;
    if(BitCastInst *BI = dyn_cast<BitCastInst>(*ui)) {
      if(isNotStored(BI))
        continue;
      else
        return false;
    }
    if(PHINode *PN = dyn_cast<PHINode>(*ui)) {
      if(isNotStored(PN))
        continue;
      else
        return false;
    }

    return false;
  }
  return true;
}

AllocIdentify::AllocIdentify() : ModulePass(ID) {}
AllocIdentify::~AllocIdentify() {}

bool AllocIdentify::runOnModule(Module& M) {

  allocators.insert("malloc");
  allocators.insert("calloc");
  //allocators.insert("realloc");
  //allocators.insert("memset");
  deallocators.insert("free");
  deallocators.insert("cfree");

  bool changed;
  do {
    changed = false;
    std::set<std::string> TempAllocators;
    TempAllocators.insert( allocators.begin(), allocators.end());
    std::set<std::string>::iterator it;
    for(it = TempAllocators.begin(); it != TempAllocators.end(); ++it) {
      Function* F = M.getFunction(*it);
      if(!F)
        continue;
      for(Value::use_iterator ui = F->use_begin(), ue = F->use_end();
          ui != ue; ++ui) {
        // iterate though all calls to malloc
        if (CallInst* CI = dyn_cast<CallInst>(*ui)) {
          // The function that calls malloc could be a potential allocator
          Function *WrapperF = CI->getParent()->getParent();
          if(WrapperF->doesNotReturn())
            continue;
          if(!(WrapperF->getReturnType()->isPointerTy()))
            continue;
          bool isWrapper = true;
          for (Function::iterator BBI = WrapperF->begin(), E = WrapperF->end(); BBI != E; ) {
            BasicBlock &BB = *BBI++;

            // Only look at return blocks.
            ReturnInst *Ret = dyn_cast<ReturnInst>(BB.getTerminator());
            if (Ret == 0) continue;

            //check for ALL return values
            if(flowsFrom(Ret, CI)) {
              continue;
            } else {
              isWrapper = false;
              break;
            }
            // if true for all return add to list of allocators
          }
          if(isWrapper)
            isWrapper = isWrapper && isNotStored(CI);
          if(isWrapper) {
            changed = (allocators.find(WrapperF->getName()) == allocators.end());
            if(changed) {
              ++numAllocators;
              allocators.insert(WrapperF->getName());
              DEBUG(errs() << WrapperF->getName().str() << "\n");
            }
          }
        }
      }
    }
  } while(changed);

  do {
    changed = false;
    std::set<std::string> TempDeallocators;
    TempDeallocators.insert( deallocators.begin(), deallocators.end());
    std::set<std::string>::iterator it;
    for(it = TempDeallocators.begin(); it != TempDeallocators.end(); ++it) {
      Function* F = M.getFunction(*it);

      if(!F)
        continue;
      for(Value::use_iterator ui = F->use_begin(), ue = F->use_end();
          ui != ue; ++ui) {
        // iterate though all calls to malloc
        if (CallInst* CI = dyn_cast<CallInst>(*ui)) {
          // The function that calls malloc could be a potential allocator
          Function *WrapperF = CI->getParent()->getParent();

          if(WrapperF->arg_size() != 1)
            continue;
          if(!WrapperF->arg_begin()->getType()->isPointerTy())
            continue;
          Argument *arg = dyn_cast<Argument>(WrapperF->arg_begin());
          if(flowsFrom(CI->getOperand(1), arg)) {
            changed = (deallocators.find(WrapperF->getName()) == deallocators.end());
            if(changed) {
              ++numDeallocators;
              deallocators.insert(WrapperF->getName());
              DEBUG(errs() << WrapperF->getName().str() << "\n");
            }
          }
        }
      }
    }
  } while(changed);
  return false;
}
void AllocIdentify::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<LoopInfo>();
  AU.setPreservesAll();
}

char AllocIdentify::ID = 0;
static RegisterPass<AllocIdentify>
X("alloc-identify", "Identify allocator wrapper functions");
