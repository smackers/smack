//===-- GEPExprArg.cpp - Promote args if they come from GEPs  -------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Identify GEPs used as arguments to call sites.
// 
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "gepexprargs"

#include "assistDS/GEPExprArgs.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Support/FormattedStream.h"
#include "smack/Debug.h"
#include <vector>
#include <map>

// Pass statistics
STATISTIC(numSimplified, "Number of Calls Modified");

using namespace llvm;

//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM pass.
//  Clone functions that take GEPs as arguments
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
bool GEPExprArgs::runOnModule(Module& M) {
  bool changed;
  do {
    changed = false;
    for (Module::iterator F = M.begin(); F != M.end(); ++F){
      for (Function::iterator B = F->begin(), FE = F->end(); B != FE; ++B) {
        for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;) {
          CallInst *CI = dyn_cast<CallInst>(I++);
          if(!CI)
            continue;

          if(CI->hasByValArgument())
            continue;
          // if the GEP calls a function, that is externally defined,
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
          unsigned argNum = 1;
          for(; argNum < CI->getNumOperands();argNum++, ++ai) {
            if(ai->use_empty())
              continue;
            if (isa<GEPOperator>(CI->getOperand(argNum)))
              break;
          }

          // if no argument was a GEP operator to be changed 
          if(ai == ae)
            continue;

          GEPOperator *GEP = dyn_cast<GEPOperator>(CI->getOperand(argNum));
          if(!GEP->hasAllConstantIndices())
            continue;

          // Construct the new Type
          // Appends the struct Type at the beginning
          std::vector<Type*>TP;
          TP.push_back(GEP->getPointerOperand()->getType());
          for(unsigned c = 1; c < CI->getNumOperands();c++) {
            TP.push_back(CI->getOperand(c)->getType());
          }

          //return type is same as that of original instruction
          FunctionType *NewFTy = FunctionType::get(CI->getType(), TP, false);
          Function *NewF;
          numSimplified++;
          if(numSimplified > 800) 
            return true;

          NewF = Function::Create(NewFTy,
                                  GlobalValue::InternalLinkage,
                                  F->getName().str() + ".TEST",
                                  &M);

          auto NI = NewF->arg_begin();
          NI->setName("GEParg");
          ++NI;

          ValueToValueMapTy ValueMap;

          for (auto II = F->arg_begin(); NI != NewF->arg_end(); ++II, ++NI) {
            ValueMap[&*II] = &*NI;
            NI->setName(II->getName());
            NI->addAttr(F->getAttributes().getParamAttributes(II->getArgNo() + 1));
          }
          NewF->setAttributes(NewF->getAttributes().addAttributes(
              F->getContext(), 0, F->getAttributes().getRetAttributes()));
          // Perform the cloning.
          SmallVector<ReturnInst*,100> Returns;
          CloneFunctionInto(NewF, F, ValueMap, false, Returns);
          std::vector<Value*> fargs;
          for (auto &Arg : NewF->args()) {
            fargs.push_back(&Arg);
          }

          NewF->setAttributes(NewF->getAttributes().addAttributes(
              F->getContext(), ~0, F->getAttributes().getFnAttributes()));
          //Get the point to insert the GEP instr.
          SmallVector<Value*, 8> Ops(CI->op_begin()+1, CI->op_end());
          Instruction *InsertPoint;
          for (Instruction *insrt = &*NewF->front().begin();
               isa<AllocaInst>(InsertPoint = insrt); ++insrt) {;}

          NI = NewF->arg_begin();
          SmallVector<Value*, 8> Indices;
          Indices.append(GEP->op_begin()+1, GEP->op_end());
          GetElementPtrInst *GEP_new = GetElementPtrInst::Create(nullptr,
                                                                 cast<Value>(NI),
                                                                 Indices, 
                                                                 "", InsertPoint);
          fargs.at(argNum)->replaceAllUsesWith(GEP_new);
          unsigned j = argNum + 1;
          for(; j < CI->getNumOperands();j++) {
            if(CI->getOperand(j) == GEP)
              fargs.at(j)->replaceAllUsesWith(GEP_new);
          }

          // Get the initial attributes of the call
          AttributeList CallPAL = CI->getAttributes();
          AttributeSet RAttrs = CallPAL.getRetAttributes();
          AttributeSet FnAttrs = CallPAL.getFnAttributes();

          SmallVector<Value*, 8> Args;
          SmallVector<AttributeSet, 8> ArgAttrs;
          Args.push_back(GEP->getPointerOperand());
          ArgAttrs.push_back(AttributeSet());
          for(unsigned j =1;j<CI->getNumOperands();j++) {
            Args.push_back(CI->getOperand(j));
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


char GEPExprArgs::ID = 0;
static RegisterPass<GEPExprArgs>
X("gep-expr-arg", "Find GEP Exprs passed as args");
