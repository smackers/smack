//===-- LoadArgs.cpp - Promote args if they came from loads ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Identify calls, that are passed arguments that are LoadInsts.
// Pass the original pointer instead. Helps improve some
// context sensitivity.
// 
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "ld-args"

#include "assistDS/LoadArgs.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Support/FormattedStream.h"
#include "smack/Debug.h"
#include <vector>
#include <set>
#include <map>

// Pass statistics
STATISTIC(numSimplified, "Number of Calls Modified");

using namespace llvm;

//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM pass.
//  Clone functions that take LoadInsts as arguments
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
bool LoadArgs::runOnModule(Module& M) {
  std::map<std::pair<Function*, const Type * > , Function* > fnCache;
  bool changed;
  do { 
    changed = false;
    for (Module::iterator Func = M.begin(); Func != M.end(); ++Func) {
      for (Function::iterator B = Func->begin(), FE = Func->end(); B != FE; ++B) {
        for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;) {
          CallInst *CI = dyn_cast<CallInst>(I++);
          if(!CI)
            continue;

          if(CI->hasByValArgument())
            continue;
          // if the CallInst calls a function, that is externally defined,
          // or might be changed, ignore this call site.
          Function *F = CI->getCalledFunction();
          if (!F || (F->isDeclaration() || F->isInterposable()))
            continue;
          if(F->hasStructRetAttr())
            continue;
          if(F->isVarArg())
            continue;

          // find the argument we must replace
          Function::arg_iterator ai = F->arg_begin(), ae = F->arg_end();
          unsigned argNum = 0;
          for(; argNum < CI->getNumArgOperands();argNum++, ++ai) {
            // do not care about dead arguments
            if(ai->use_empty())
              continue;
            if(F->getAttributes().getParamAttributes(argNum).hasAttrSomewhere(Attribute::SExt) ||
               F->getAttributes().getParamAttributes(argNum).hasAttrSomewhere(Attribute::ZExt))
              continue;
            if (isa<LoadInst>(CI->getArgOperand(argNum)))
              break;
          }

          // if no argument was a GEP operator to be changed 
          if(ai == ae)
            continue;

          LoadInst *LI = dyn_cast<LoadInst>(CI->getArgOperand(argNum));
          Instruction * InsertPt = &(Func->getEntryBlock().front());
          AllocaInst *NewVal = new AllocaInst(LI->getType(), "",InsertPt);

          StoreInst *Copy = new StoreInst(LI, NewVal);
          Copy->insertAfter(LI);
          /*if(LI->getParent() != CI->getParent())
            continue;
          // Also check that there is no store after the load.
          // TODO: Check if the load/store do not alias.
          BasicBlock::iterator bii = LI->getParent()->begin();
          Instruction *BII = bii;
          while(BII != LI) {
            ++bii;
            BII = bii;
          }
          while(BII != CI) {
            if(isa<StoreInst>(BII))
              break;
            ++bii;
            BII = bii;
          }
          if(isa<StoreInst>(bii)){
            continue;
          }*/

          // Construct the new Type
          // Appends the struct Type at the beginning
          std::vector<Type*>TP;
          for(unsigned c = 0; c < CI->getNumArgOperands();c++) {
            if(c == argNum)
              TP.push_back(LI->getPointerOperand()->getType());
            TP.push_back(CI->getArgOperand(c)->getType());
          }

          //return type is same as that of original instruction
          FunctionType *NewFTy = FunctionType::get(CI->getType(), TP, false);
          numSimplified++;
          //if(numSimplified > 1000)
          //return true;

          Function *NewF;
          std::map<std::pair<Function*, const Type* > , Function* >::iterator Test;
          Test = fnCache.find(std::make_pair(F, NewFTy));
          if(Test != fnCache.end()) {
            NewF = Test->second;
          } else {
            NewF = Function::Create(NewFTy,
                                    GlobalValue::InternalLinkage,
                                    F->getName().str() + ".TEST",
                                    &M);

            fnCache[std::make_pair(F, NewFTy)] = NewF;
            auto NI = NewF->arg_begin();

            ValueToValueMapTy ValueMap;

            unsigned count = 0;
            for (auto II = F->arg_begin(); NI != NewF->arg_end(); ++count, ++NI) {
              if(count == argNum) {
                NI->setName("LDarg");
                continue;
              }
              ValueMap[&*II] = &*NI;
              NI->setName(II->getName());
              NI->addAttr(F->getAttributes().getParamAttributes(II->getArgNo() + 1));
              ++II;
            }
            // Perform the cloning.
            SmallVector<ReturnInst*,100> Returns;
            CloneFunctionInto(NewF, F, ValueMap, false, Returns);
            std::vector<Value*> fargs;
            for (auto &Arg : NewF->args()) {
              fargs.push_back(&Arg);
            }

            NewF->setAttributes(NewF->getAttributes().addAttributes(
                F->getContext(), 0, F->getAttributes().getRetAttributes()));
            NewF->setAttributes(NewF->getAttributes().addAttributes(
                F->getContext(), ~0, F->getAttributes().getFnAttributes()));
            //Get the point to insert the GEP instr.
            Instruction *InsertPoint;
            for (auto insrt = NewF->front().begin(); isa<AllocaInst>(InsertPoint = &*insrt); ++insrt) {;}
            LoadInst *LI_new = new LoadInst(fargs.at(argNum), "", InsertPoint);
            fargs.at(argNum+1)->replaceAllUsesWith(LI_new);
          }

          // Get the initial attributes of the call
          AttributeList CallPAL = CI->getAttributes();
          AttributeSet RAttrs = CallPAL.getRetAttributes();
          AttributeSet FnAttrs = CallPAL.getFnAttributes();
          
          SmallVector<Value*, 8> Args;
          SmallVector<AttributeSet, 8> ArgAttrs;
          for(unsigned j =0;j<CI->getNumArgOperands();j++) {
            if(j == argNum) {
              Args.push_back(NewVal);
              ArgAttrs.push_back(AttributeSet());
            }
            Args.push_back(CI->getArgOperand(j));
            ArgAttrs.push_back(CallPAL.getParamAttributes(j));
          }

          auto NewCallPAL = AttributeList::get(F->getContext(), FnAttrs, RAttrs, ArgAttrs);
          CallInst *CallI = CallInst::Create(NewF,Args,"", CI);
          CallI->setCallingConv(CI->getCallingConv());
          CallI->setAttributes(NewCallPAL);
          CI->replaceAllUsesWith(CallI);
          CI->eraseFromParent();
          changed = true;
        }
      }
    }
  } while(changed);
  return true;
}

char LoadArgs::ID = 0;
static RegisterPass<LoadArgs>
X("ld-args", "Find Load Inst passed as args");
