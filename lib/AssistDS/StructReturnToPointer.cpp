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
#include "llvm/Attributes.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/ValueMap.h"
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

  std::vector<Function*> worklist;
  for (Module::iterator I = M.begin(); I != M.end(); ++I)
    if (!I->isDeclaration() && !I->mayBeOverridden()) {
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
                                    GlobalValue::InternalLinkage, 
                                    F->getName(), &M);
    ValueToValueMapTy ValueMap;
    Function::arg_iterator NI = NF->arg_begin();
    NI->setName("ret");
    ++NI;
    for (Function::arg_iterator II = F->arg_begin(); II != F->arg_end(); ++II, ++NI) {
      ValueMap[II] = NI;
      NI->setName(II->getName());
      NI->addAttr(F->getAttributes().getParamAttributes(II->getArgNo() + 1));
    }
    // Perform the cloning.
    SmallVector<ReturnInst*,100> Returns;
    CloneFunctionInto(NF, F, ValueMap, false, Returns);
    std::vector<Value*> fargs;
    for(Function::arg_iterator ai = NF->arg_begin(), 
        ae= NF->arg_end(); ai != ae; ++ai) {
      fargs.push_back(ai);
    }
    NF->setAttributes(NF->getAttributes().addAttr(
        M.getContext(), 0, F->getAttributes().getRetAttributes()));
    NF->setAttributes(NF->getAttributes().addAttr(
        M.getContext(), ~0, F->getAttributes().getFnAttributes()));
    
    for (Function::iterator B = NF->begin(), FE = NF->end(); B != FE; ++B) {      
      for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;) {
        ReturnInst * RI = dyn_cast<ReturnInst>(I++);
        if(!RI)
          continue;
        new StoreInst(RI->getOperand(0), fargs.at(0), RI);
      }
    }

    for(Value::use_iterator ui = F->use_begin(), ue = F->use_end();
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

      SmallVector<AttributeWithIndex, 8> AttributesVec;

      // Get the initial attributes of the call
      AttrListPtr CallPAL = CI->getAttributes();
      Attributes RAttrs = CallPAL.getRetAttributes();
      Attributes FnAttrs = CallPAL.getFnAttributes();
      
      if (RAttrs.hasAttributes())
        AttributesVec.push_back(AttributeWithIndex::get(0, RAttrs));

      Args.push_back(AllocaNew);
      for(unsigned j =1;j<CI->getNumOperands();j++) {
        Args.push_back(CI->getOperand(j));
        // position in the AttributesVec
        Attributes Attrs = CallPAL.getParamAttributes(j);
        if (Attrs.hasAttributes())
          AttributesVec.push_back(AttributeWithIndex::get(Args.size(), Attrs));
      }
      // Create the new attributes vec.
      if (FnAttrs.hasAttributes())
        AttributesVec.push_back(AttributeWithIndex::get(~0, FnAttrs));

      AttrListPtr NewCallPAL = AttrListPtr::get(F->getContext(),
                                                AttributesVec);

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
