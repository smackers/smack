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


#include "llvm/IR/Constants.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/DataLayout.h"

#include "seadsa/CompleteCallGraph.hh"

#include <set>

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
      seadsa::CompleteCallGraph *CCG;

      // Access to the target data analysis pass
      const DataLayout * TD;

      // Worklist of call sites to transform
      std::vector<CallBase *> Worklist;

      // A cache of indirect call targets that have been converted already
      std::map<const Function *, std::set<const Function *> > bounceCache;

    protected:
      void makeDirectCall (CallBase *CS);
      Function* buildBounce (CallBase *CS,std::vector<const Function*>& Targets);
      const Function* findInCache (const CallBase *CS,
                                   std::set<const Function*>& Targets);

    public:
      static char ID;
      Devirtualize() : ModulePass(ID) {}

      virtual bool runOnModule(Module & M) override;

      virtual void getAnalysisUsage(AnalysisUsage &AU) const override{
        AU.addRequired<seadsa::CompleteCallGraph>();
      }

      // Visitor methods for analyzing instructions
      //void visitInstruction(Instruction &I);
      void processCallSite(CallBase *CS);
      void visitCallInst(CallInst &CI) {
        processCallSite(&CI);
      }
      void visitInvokeInst(InvokeInst &II) {
        processCallSite(&II);
      }
  };
}

