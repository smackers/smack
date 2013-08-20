//===-------- ArgCast.cpp - Cast Arguments to Calls -----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
// Convert 
// call(bitcast (.., T1 arg, ...)F to(..., T2 arg, ...))(..., T2 val, ...)
// to
// val1 = bitcast T2 val to T1
// call F (..., T1 val1, ...)
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "argcast"

#include "assistDS/ArgCast.h"
#include "llvm/Attributes.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"

#include <set>
#include <map>
#include <vector>

using namespace llvm;

// Pass statistics
STATISTIC(numChanged,   "Number of Args bitcasted");

//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM pass.
//  Search for all call sites to casted functions.
//  Check if they only differ in an argument type
//  Cast the argument, and call the original function
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
bool ArgCast::runOnModule(Module& M) {

  std::vector<CallInst*> worklist;
  for (Module::iterator I = M.begin(); I != M.end(); ++I) {
    if (I->mayBeOverridden())
      continue;
    // Find all uses of this function
    for(Value::use_iterator ui = I->use_begin(), ue = I->use_end(); ui != ue; ) {
      // check if is ever casted to a different function type
      ConstantExpr *CE = dyn_cast<ConstantExpr>(*ui++);
      if(!CE)
        continue;
      if (CE->getOpcode() != Instruction::BitCast)
        continue;
      if(CE->getOperand(0) != I)
        continue;
      const PointerType *PTy = dyn_cast<PointerType>(CE->getType());
      if (!PTy)
        continue;
      const Type *ETy = PTy->getElementType();
      const FunctionType *FTy  = dyn_cast<FunctionType>(ETy); 
      if(!FTy)
        continue;
      // casting to a varargs funtion
      // or function with same number of arguments
      // possibly varying types of arguments
      
      if(FTy->getNumParams() != I->arg_size() && !FTy->isVarArg())
        continue;
      for(Value::use_iterator uii = CE->use_begin(),
          uee = CE->use_end(); uii != uee; ++uii) {
        // Find all uses of the casted value, and check if it is 
        // used in a Call Instruction
        if (CallInst* CI = dyn_cast<CallInst>(*uii)) {
          // Check that it is the called value, and not an argument
          if(CI->getCalledValue() != CE) 
            continue;
          // Check that the number of arguments passed, and expected
          // by the function are the same.
          if(!I->isVarArg()) {
            if(CI->getNumOperands() != I->arg_size() + 1)
              continue;
          } else {
            if(CI->getNumOperands() < I->arg_size() + 1)
              continue;
          }
          // If so, add to worklist
          worklist.push_back(CI);
        }
      }
    }
  }

  // Proces the worklist of potential call sites to transform
  while(!worklist.empty()) {
    CallInst *CI = worklist.back();
    worklist.pop_back();
    // Get the called Function
    Function *F = cast<Function>(CI->getCalledValue()->stripPointerCasts());
    const FunctionType *FTy = F->getFunctionType();

    SmallVector<Value*, 8> Args;
    unsigned i =0;
    for(i =0; i< FTy->getNumParams(); ++i) {
      Type *ArgType = CI->getOperand(i+1)->getType();
      Type *FormalType = FTy->getParamType(i);
      // If the types for this argument match, just add it to the
      // parameter list. No cast needs to be inserted.
      if(ArgType == FormalType) {
        Args.push_back(CI->getOperand(i+1));
      }
      else if(ArgType->isPointerTy() && FormalType->isPointerTy()) {
        CastInst *CastI = CastInst::CreatePointerCast(CI->getOperand(i+1), 
                                                      FormalType, "", CI);
        Args.push_back(CastI);
      } else if (ArgType->isIntegerTy() && FormalType->isIntegerTy()) {
        unsigned SrcBits = ArgType->getScalarSizeInBits();
        unsigned DstBits = FormalType->getScalarSizeInBits();
        if(SrcBits > DstBits) {
          CastInst *CastI = CastInst::CreateIntegerCast(CI->getOperand(i+1), 
                                                        FormalType, true, "", CI);
          Args.push_back(CastI);
        } else {
          if(F->getParamAttributes(i+1).SExt) {
            CastInst *CastI = CastInst::CreateIntegerCast(CI->getOperand(i+1), 
                                                          FormalType, true, "", CI);
            Args.push_back(CastI);
          } else if(F->getParamAttributes(i+1).ZExt) {
            CastInst *CastI = CastInst::CreateIntegerCast(CI->getOperand(i+1), 
                                                          FormalType, false, "", CI);
            Args.push_back(CastI);
          } else {
            // Use ZExt in default case.
            // Derived from InstCombine. Also, the only reason this should happen
            // is mismatched prototypes.
            // Seen in case of integer constants which get interpreted as i32, 
            // even if being used as i64.
            // TODO: is this correct?
            CastInst *CastI = CastInst::CreateIntegerCast(CI->getOperand(i+1), 
                                                          FormalType, false, "", CI);
            Args.push_back(CastI);
          } 
        } 
      } else {
        DEBUG(ArgType->dump());
        DEBUG(FormalType->dump());
        break;
      }
    }

    // If we found an argument we could not cast, try the next instruction
    if(i != FTy->getNumParams()) {
      continue;
    }

    if(FTy->isVarArg()) {
      for(; i< CI->getNumOperands() - 1 ;i++) {
        Args.push_back(CI->getOperand(i+1));
      }
    }

    // else replace the call instruction
    CallInst *CINew = CallInst::Create(F, Args, "", CI);
    CINew->setCallingConv(CI->getCallingConv());
    CINew->setAttributes(CI->getAttributes());
    if(!CI->use_empty()) {
      CastInst *RetCast;
      if(CI->getType() != CINew->getType()) {
        if(CI->getType()->isPointerTy() && CINew->getType()->isPointerTy())
          RetCast = CastInst::CreatePointerCast(CINew, CI->getType(), "", CI);
        else if(CI->getType()->isIntOrIntVectorTy() && CINew->getType()->isIntOrIntVectorTy())
          RetCast = CastInst::CreateIntegerCast(CINew, CI->getType(), false, "", CI);
        else if(CI->getType()->isIntOrIntVectorTy() && CINew->getType()->isPointerTy())
          RetCast = CastInst::CreatePointerCast(CINew, CI->getType(), "", CI);
        else if(CI->getType()->isPointerTy() && CINew->getType()->isIntOrIntVectorTy()) 
          RetCast = new IntToPtrInst(CINew, CI->getType(), "", CI);
        else {
          // TODO: I'm not sure what right behavior is here, but this case should be handled.
          assert(0 && "Unexpected type conversion in call!");
          abort();
        }
        CI->replaceAllUsesWith(RetCast);
      } else {
        CI->replaceAllUsesWith(CINew);
      }
    }

    // Debug printing
    DEBUG(errs() << "ARGCAST:");
    DEBUG(errs() << "ERASE:");
    DEBUG(CI->dump());
    DEBUG(errs() << "ARGCAST:");
    DEBUG(errs() << "ADDED:");
    DEBUG(CINew->dump());

    CI->eraseFromParent();
    numChanged++;
  }
  return true;
}

// Pass ID variable
char ArgCast::ID = 0;

// Register the pass
static RegisterPass<ArgCast>
X("arg-cast", "Cast Arguments");
