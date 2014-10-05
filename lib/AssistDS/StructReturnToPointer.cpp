//===-------- StructReturnToPointer.cpp ------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// For functions that return structures,
// transform them to return a pointer to the structure instead.
//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "struct-ret"

#include "assistDS/StructReturnToPointer.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"

#include <set>
#include <map>
#include <vector>

using namespace llvm;


//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM pass.
//  If a function returns a struct, make it return
//  a pointer to the struct.
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
bool StructRet::runOnModule(Module& M) {
  const llvm::DataLayout targetData(&M);

  std::vector<Function*> worklist;
  for (Module::iterator I = M.begin(); I != M.end(); ++I)
    if (!I->mayBeOverridden()) {
      if(I->hasAddressTaken())
        continue;
      if(I->getReturnType()->isStructTy()) {
        worklist.push_back(I);
      }
    }

  while(!worklist.empty()) {
    Function *F = worklist.back();
    worklist.pop_back();
    Type *NewArgType = F->getReturnType()->getPointerTo();

    // Construct the new Type
    std::vector<Type*>TP;
    TP.push_back(NewArgType);
    for (Function::arg_iterator ii = F->arg_begin(), ee = F->arg_end();
         ii != ee; ++ii) {
      TP.push_back(ii->getType());
    }

    FunctionType *NFTy = FunctionType::get(F->getReturnType(), TP, F->isVarArg());

    // Create the new function body and insert it into the module.
    Function *NF = Function::Create(NFTy, 
                                    F->getLinkage(),
                                    F->getName(), &M);
    ValueToValueMapTy ValueMap;
    Function::arg_iterator NI = NF->arg_begin();
    NI->setName("ret");
    ++NI;
    for (Function::arg_iterator II = F->arg_begin(); II != F->arg_end(); ++II, ++NI) {
      ValueMap[II] = NI;
      NI->setName(II->getName());
      AttributeSet attrs = F->getAttributes().getParamAttributes(II->getArgNo() + 1);
      if (!attrs.isEmpty())
        NI->addAttr(attrs);
    }
    // Perform the cloning.
    SmallVector<ReturnInst*,100> Returns;
    if (!F->isDeclaration())
      CloneFunctionInto(NF, F, ValueMap, false, Returns);
    std::vector<Value*> fargs;
    for(Function::arg_iterator ai = NF->arg_begin(), 
        ae= NF->arg_end(); ai != ae; ++ai) {
      fargs.push_back(ai);
    }
    NF->setAttributes(NF->getAttributes().addAttributes(
        M.getContext(), 0, F->getAttributes().getRetAttributes()));
    NF->setAttributes(NF->getAttributes().addAttributes(
        M.getContext(), ~0, F->getAttributes().getFnAttributes()));
    
    for (Function::iterator B = NF->begin(), FE = NF->end(); B != FE; ++B) {      
      for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;) {
        ReturnInst * RI = dyn_cast<ReturnInst>(I++);
        if(!RI)
          continue;
        LoadInst *LI = dyn_cast<LoadInst>(RI->getOperand(0));
        assert(LI && "Return should be preceded by a load instruction");
        IRBuilder<> Builder(RI);
        Builder.CreateMemCpy(fargs.at(0),
            LI->getPointerOperand(),
            targetData.getTypeStoreSize(LI->getType()),
            targetData.getPrefTypeAlignment(LI->getType()));
      }
    }

    for(Value::user_iterator ui = F->user_begin(), ue = F->user_end();
        ui != ue; ) {
      CallInst *CI = dyn_cast<CallInst>(*ui++);
      if(!CI)
        continue;
      if(CI->getCalledFunction() != F)
        continue;
      if(CI->hasByValArgument())
        continue;
      AllocaInst *AllocaNew = new AllocaInst(F->getReturnType(), 0, "", CI);
      SmallVector<Value*, 8> Args;

      //this should probably be done in a different manner
      AttributeSet NewCallPAL=AttributeSet();
      
      // Get the initial attributes of the call
      AttributeSet CallPAL = CI->getAttributes();
      AttributeSet RAttrs = CallPAL.getRetAttributes();
      AttributeSet FnAttrs = CallPAL.getFnAttributes();
      
      if (!RAttrs.isEmpty())
        NewCallPAL=NewCallPAL.addAttributes(F->getContext(),0, RAttrs);

      Args.push_back(AllocaNew);
      for(unsigned j = 0; j < CI->getNumOperands()-1; j++) {
        Args.push_back(CI->getOperand(j));
        // position in the NewCallPAL
        AttributeSet Attrs = CallPAL.getParamAttributes(j);
        if (!Attrs.isEmpty())
          NewCallPAL=NewCallPAL.addAttributes(F->getContext(),Args.size(), Attrs);
      }
      // Create the new attributes vec.
      if (!FnAttrs.isEmpty())
        NewCallPAL=NewCallPAL.addAttributes(F->getContext(),~0, FnAttrs);

      CallInst *CallI = CallInst::Create(NF, Args, "", CI);
      CallI->setCallingConv(CI->getCallingConv());
      CallI->setAttributes(NewCallPAL);
      LoadInst *LI = new LoadInst(AllocaNew, "", CI);
      CI->replaceAllUsesWith(LI);
      CI->eraseFromParent();
    }
    if(F->use_empty())
      F->eraseFromParent();
  }
  return true;
}

// Pass ID variable
char StructRet::ID = 0;

// Register the pass
static RegisterPass<StructRet>
X("struct-ret", "Find struct arguments");
