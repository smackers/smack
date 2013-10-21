//===- Devirt.cpp - Devirtualize using the sig match intrinsic in llva ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "devirt"
#include "llvm/IR/Constants.h"
#include "llvm/Transforms/IPO.h"
#include "dsa/CallTargets.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/Statistic.h"

#include <iostream>
#include <algorithm>
#include <iterator>

using namespace llvm;

#if 0

//
// Function: castTo()
//
// Description: //  Given an LLVM value, insert a cast instruction to make it a given type.
//
static inline Value *
castTo (Value * V, const Type * Ty, Instruction * InsertPt) {   //
  // Don't bother creating a cast if it's already the correct type.
  //
  if (V->getType() == Ty)
    return V;

  //
  // If it's a constant, just create a constant expression.
  //
  if (Constant * C = dyn_cast<Constant>(V)) {
    Constant * CE = ConstantExpr::getCast (C, Ty);
    return CE;
  }

  //
  // Otherwise, insert a cast instruction.
  //
  return new CastInst::Create(V, Ty, "cast", InsertPt);
}

namespace {

  static cl::opt<int>
  VirtualLimit("devirt-limit", cl::Hidden, cl::init(16),
               cl::desc("Maximum number of callees to devirtualize at a call site"));
  STATISTIC(FuncAdded, "Number of bounce functions added");
  STATISTIC(CSConvert, "Number of call sites converted");


  class Devirtualize : public ModulePass {


    Function * IndirectFuncFail;

    std::map<std::pair<const Type*, std::vector<Function*> >, Function*> cache;
    int fnum;

    //
    // Method: buildBounce()
    //
    // Description:
    //  Replaces the given call site with a call to a bounce function.  The
    //  bounce function compares the function pointer to one of the given
    //  target functions and calls the function directly if the pointer
    //  matches.
    Function* buildBounce (CallSite cs,
                           std::vector<Function*>& Targets,
                           Module& M) {

      Value* ptr = cs.getCalledValue();
      const FunctionType* OrigType = 
        cast<FunctionType>(cast<PointerType>(ptr->getType())->getElementType());;
      ++FuncAdded;

      std::vector< const Type *> TP(OrigType->param_begin(), OrigType->param_end());
      TP.insert(TP.begin(), ptr->getType());
      const FunctionType* NewTy = FunctionType::get(OrigType->getReturnType(), TP, false);
      Function* F = new Function(NewTy, GlobalValue::InternalLinkage, "devirtbounce", &M);
      std::map<Function*, BasicBlock*> targets;

      F->arg_begin()->setName("funcPtr");
      std::vector<Value*> fargs;
      for(Function::arg_iterator ai = F->arg_begin(), ae = F->arg_end(); ai != ae; ++ai)
        if (ai != F->arg_begin()) {
          fargs.push_back(ai);
          ai->setName("arg");
        }

      for (std::vector<Function*>::iterator i = Targets.begin(), e = Targets.end();
           i != e; ++i) {
        Function* FL = *i;
        BasicBlock* BL = new BasicBlock(FL->getName(), F);
        targets[FL] = BL;

        //Make call
        Value* call = new CallInst(FL, fargs, "", BL);

        //return correctly
        if (OrigType->getReturnType() == Type::VoidTy)
          new ReturnInst(0, BL);
        else
          new ReturnInst(call, BL);
      }

      // Create a set of tests that search for the correct function target
      // and call it directly.  If none of the target functions match,
      // call pchk_ind_fail() to note the failure.

      //
      // Create the failure basic block.  Then, add the following:
      //  o the terminating instruction
      //  o the indirect call to the original function
      //  o a call to phck_ind_fail()
      //
      BasicBlock* tail = new BasicBlock("fail", F, &F->getEntryBlock());
      Instruction * InsertPt;
#if 0
      InsertPt = new UnreachableInst(tail);
#else
      Value* p = F->arg_begin();
      Instruction * realCall = new CallInst (p, fargs, "", tail);
      if (OrigType->getReturnType() == Type::VoidTy)
        InsertPt = new ReturnInst(0, tail);
      else
        InsertPt = new ReturnInst(realCall, tail);
#endif
      Value * FuncVoidPtr = castTo (p,
                                    PointerType::get(Type::SByteTy),
                                    realCall);
      new CallInst (IndirectFuncFail, FuncVoidPtr, "", realCall);
      

      // Create basic blocks for valid target functions
      for (std::vector<Function*>::iterator i = Targets.begin(), e = Targets.end();
           i != e; ++i) {
        BasicBlock* TB = targets[*i];
        BasicBlock* newB = new BasicBlock("test." + (*i)->getName(), F, &F->getEntryBlock());
        SetCondInst* setcc = new SetCondInst(Instruction::SetEQ, *i, p, "sc", newB);
        new BranchInst(TB, tail, setcc, newB);
        tail = newB;
      }
      return F;
    }

  public:
    static char ID;
    Devirtualize() : ModulePass(&ID) {}

    virtual bool runOnModule(Module &M) {
      CallTargetFinder* CTF = &getAnalysis<CallTargetFinder>();

      // Get references to functions that are needed in the module
      Function* ams = M.getNamedFunction ("llva_assert_match_sig");
      if (!ams)
        return false;

      IndirectFuncFail = M.getOrInsertFunction ("pchk_ind_fail",
                                                Type::VoidTy,
                                                PointerType::getUnqual(Type::Int8Ty),
                                                NULL);
      
      std::set<Value*> safecalls;
      std::vector<Instruction*> toDelete;

      for (Value::use_iterator ii = ams->use_begin(), ee = ams->use_end();
           ii != ee; ++ii) {
        if (CallInst* CI = dyn_cast<CallInst>(*ii)) {
          std::cerr << "Found safe call site in " 
                    << CI->getParent()->getParent()->getName() << "\n";
          Value* V = CI->getOperand(1);
          toDelete.push_back(CI);
          do {
            //V->dump();
            safecalls.insert(V);
            if (CastInst* CV = dyn_cast<CastInst>(V))
              V = CV->getOperand(0);
            else V = 0;
          } while (V);
        }
      }

      for(std::set<Value*>::iterator i = safecalls.begin(), e = safecalls.end();
          i != e; ++i) {
        for (Value::use_iterator uii = (*i)->use_begin(), uie = (*i)->use_end();
             uii != uie; ++uii) {
          CallSite cs = CallSite::get(*uii);
          bool isSafeCall = cs.getInstruction() && 
            safecalls.find(cs.getCalledValue()) != safecalls.end();
          if (cs.getInstruction() && !cs.getCalledFunction() &&
              (isSafeCall || CTF->isComplete(cs))) {
            std::vector<const Function*> Targets;
            for (std::vector<const Function*>::iterator ii = CTF->begin(cs), ee = CTF->end(cs);
                 ii != ee; ++ii)
              if (!isSafeCall || (*ii)->getType() == cs.getCalledValue()->getType())
                Targets.push_back(*ii);

            if (Targets.size() > 0) {
              std::cerr << "Target count: " << Targets.size() << " in " << cs.getInstruction()->getParent()->getParent()->getName() << "\n";
              Function* NF = buildBounce(cs, Targets, M);
              if (CallInst* ci = dyn_cast<CallInst>(cs.getInstruction())) {
                ++CSConvert;
                std::vector<Value*> Par(ci->op_begin(), ci->op_end());
                CallInst* cn = CallInst::Create(NF, Par.begin(), Par.end(),
                                                ci->getName() + ".dv", ci);
                ci->replaceAllUsesWith(cn);
                toDelete.push_back(ci);
              } else if (InvokeInst* ci = dyn_cast<InvokeInst>(cs.getInstruction())) {
                ++CSConvert;
                std::vector<Value*> Par(ci->op_begin(), ci->op_end());
                InvokeInst* cn = InvokeInst::Create(NF, ci->getNormalDest(),
                                                    ci->getUnwindDest(),
                                                    Par, ci->getName()+".dv",
                                                    ci);
                ci->replaceAllUsesWith(cn);
                toDelete.push_back(ci);
              }
            } else //Target size == 0
              std::cerr << "Call site found, but no Targets\n";
          }
        }
      }

      bool changed = false;
      for (std::vector<Instruction*>::iterator ii = toDelete.begin(), ee = toDelete.end();
           ii != ee; ++ii) {
        changed = true;
        (*ii)->eraseFromParent();
      }
      return changed;
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<CallTargetFinder>();
    }

  };

  RegisterPass<Devirtualize> X("devirt", "Devirtualization");

}

#endif
