//===-- ArgSimplify.cpp - Special case for conditional ptr args ----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "argsimpl"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"

#include <set>
#include <map>
#include <vector>

using namespace llvm;

STATISTIC(numTransformable,   "Number of Args changeable");

namespace {

  // F - Function to modify
  // arg_count - The argument to function I that may be changed
  // type - Declared type of the argument

  static void simplify(Function *F, unsigned arg_count, Type* type) {

    // Go through all uses of the function
    for(Value::use_iterator ui = F->use_begin(), ue = F->use_end();
        ui != ue; ++ui) {

      if (Constant *C = dyn_cast<Constant>(*ui)) {
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
          if (CE->getOpcode() == Instruction::BitCast) {
            if(CE->getOperand(0) == F) {                    
              for(Value::use_iterator uii = CE->use_begin(), uee = CE->use_end();
                  uii != uee; ) {
                // check if it is ever used as a call (bitcast F to ...)()
                if (CallInst* CI = dyn_cast<CallInst>(*uii++)) {
                  if(CI->getCalledValue() == CE) {
                    // if I is ever called as a bitcasted function
                    if(F->getReturnType() == CI->getType()){
                      // if the return types match.
                      if(F->arg_size() == (CI->getNumOperands()-1)){
                        // and the numeber of args match too
                        unsigned arg_count1 = 1;
                        bool change = true;
                        for (Function::arg_iterator ii1 = F->arg_begin(), ee1 = F->arg_end();
                             ii1 != ee1; ++ii1,arg_count1++) {
                          if(arg_count1 == (arg_count + 1)) {
                            if(ii1->getType() == CI->getOperand(arg_count1)->getType()){
                              change = false;
                              break;
                            }
                            else 
                              continue;
                          }
                          if(ii1->getType() != CI->getOperand(arg_count1)->getType()) {
                            change = false;
                            break;
                          }
                        }
                        // if all types match except the argument we are interested in

                        if(change){
                          // create a new function, to do the cast from ptr to int,
                          // and call the original function, with the casted value
                          std::vector<Type*>TP;
                          for(unsigned c = 1; c<CI->getNumOperands();c++) {
                            TP.push_back(CI->getOperand(c)->getType());
                          }
                          FunctionType *NewFTy = FunctionType::
                            get(CI->getType(), TP, false);
                          
                          Module *M = F->getParent();
                          Function *NewF = Function::Create(NewFTy,
                                                            GlobalValue::InternalLinkage,
                                                            "argbounce",
                                                            M);
                          std::vector<Value*> fargs;
                          for(Function::arg_iterator ai = NewF->arg_begin(), 
                              ae= NewF->arg_end(); ai != ae; ++ai) {
                            fargs.push_back(ai);
                            ai->setName("arg");
                          }
                          Value *CastedVal;
                          BasicBlock* entryBB = BasicBlock::
                            Create (M->getContext(), "entry", NewF);
                       
                          Type *FromTy = fargs.at(arg_count)->getType();
                          if(FromTy->isPointerTy()) {
                            CastedVal = CastInst::CreatePointerCast(fargs.at(arg_count), 
                                                         type, "castd", entryBB);
                          } else {
                            CastedVal = CastInst::CreateIntegerCast(fargs.at(arg_count), 
                                                                    type, false, "casted", entryBB);
                          }

                          SmallVector<Value*, 8> Args;
                          for(Function::arg_iterator ai = NewF->arg_begin(),
                              ae= NewF->arg_end(); ai != ae; ++ai) {
                            if(ai->getArgNo() == arg_count)
                              Args.push_back(CastedVal);
                            else 
                              Args.push_back(ai);
                          }

                          CallInst * CallI = CallInst::Create(F,Args, 
                                                              "", entryBB);
                          if(CallI->getType()->isVoidTy())
                            ReturnInst::Create(M->getContext(), entryBB);
                          else 
                            ReturnInst::Create(M->getContext(), CallI, entryBB);

                          CI->setCalledFunction(NewF);
                          numTransformable++;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  class ArgSimplify : public ModulePass {
  public:
    static char ID;
    ArgSimplify() : ModulePass(ID) {}

    bool runOnModule(Module& M) {

      for (Module::iterator I = M.begin(); I != M.end(); ++I) 
        if (!I->isDeclaration() && !I->mayBeOverridden()) {
          if(I->getName().str() == "main")
            continue;
          std::vector<unsigned> Args;
          for (Function::arg_iterator ii = I->arg_begin(), ee = I->arg_end();
               ii != ee; ++ii) {
            bool change = true;
            for(Value::use_iterator ui = ii->use_begin(), ue = ii->use_end();
                ui != ue; ++ui) {
              // check if the argument is used exclusively in ICmp Instructions
              if(!isa<ICmpInst>(*ui)){
                change = false;
                break;
              }
            }
            // if this argument is only used in ICMP instructions, we can
            // replace it.
            if(change) {
              simplify(I, ii->getArgNo(), ii->getType()); 
            }
          }
        }


      return true;
    }
  };
}

char ArgSimplify::ID = 0;
static RegisterPass<ArgSimplify>
X("arg-simplify", "Specialize for Conditional Arguments");
