//===- Devirt.cpp - Devirtualize using the sig match intrinsic in llva ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines an LLVM transform that converts indirect function calls
// into direct function calls.
//
//===----------------------------------------------------------------------===//

#include "dsa/CallTargets.h"

#include "llvm/IR/Constants.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/InstVisitor.h"
#include "llvm/IR/DataLayout.h"

using namespace llvm;

namespace llvm {
  //
  // Class: Devirtualize
  //
  // Description:
  //  This transform pass will look for indirect function calls and transform
  //  them into a switch statement that selects one of several direct function
  //  calls to execute.
  //
  class Devirtualize : public ModulePass, public InstVisitor<Devirtualize> {
    private:
      // Access to analysis pass which finds targets of indirect function calls
      dsa::CallTargetFinder<EQTDDataStructures> *CTF;

      // Access to the target data analysis pass
      DataLayout * TD;

      // Worklist of call sites to transform
      std::vector<Instruction *> Worklist;

      // A cache of indirect call targets that have been converted already
      std::map<const Function *, std::set<const Function *> > bounceCache;

    protected:
      void makeDirectCall (CallSite & CS);
      Function* buildBounce (CallSite cs,std::vector<const Function*>& Targets);
      const Function* findInCache (const CallSite & CS,
                                   std::set<const Function*>& Targets);

    public:
      static char ID;
      Devirtualize() : ModulePass(ID), CTF(0) {}

      virtual bool runOnModule(Module & M);

      virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.addRequired<dsa::CallTargetFinder<EQTDDataStructures> >();
        AU.addRequired<DataLayout>();
      }

      // Visitor methods for analyzing instructions
      //void visitInstruction(Instruction &I);
      void visitCallSite(CallSite &CS);
      void visitCallInst(CallInst &CI) {
        CallSite CS(&CI);
        visitCallSite(CS);
      }
      void visitInvokeInst(InvokeInst &II) {
        CallSite CS(&II);
        visitCallSite(CS);
      }
  };
}

