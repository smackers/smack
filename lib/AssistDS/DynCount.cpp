//===- Dyncount.cpp - Test pass for using constraints -----------*- C++ -*-===//
//
//                          The SAFECode Compiler
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements a test pass which helps test the generation of formulas
// and constraints.
//
//===----------------------------------------------------------------------===//

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "dsa/TypeSafety.h"

using namespace llvm;
class Dyncount : public ModulePass {
protected:
  void instrumentLoad (GlobalVariable * Counter, LoadInst * LI);
  void instrumentStore (GlobalVariable * Counter, StoreInst * SI);
  dsa::TypeSafety<TDDataStructures> *TS;

public:
  static char ID;
  Dyncount () : ModulePass (ID) { }
  const char *getPassName() const {
    return "Count safe/unsafe load/store";
  }
  virtual bool runOnModule (Module & M);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<DataLayout>();
    AU.addRequired<dsa::TypeSafety<TDDataStructures> >();
  }
};

char Dyncount::ID = 0;
static RegisterPass<Dyncount>
X ("dyncount", "Instrument code to count number of Load/Stores");


void
Dyncount::instrumentLoad (GlobalVariable * Counter, LoadInst * LI) {
  //
  // Generate a load, increment, and store right before the GEP.
  //
  LLVMContext & Context = Counter->getParent()->getContext();
  ConstantInt * One = ConstantInt::get (Type::getInt64Ty(Context), 1); 
  LoadInst * OldValue = new LoadInst (Counter, "count", LI);
  Instruction * NewValue = BinaryOperator::Create (BinaryOperator::Add,
                                                   OldValue,
                                                   One,
                                                   "count",
                                                   LI);
  new StoreInst (NewValue, Counter, LI);
  return;
}
void
Dyncount::instrumentStore (GlobalVariable * Counter, StoreInst * SI) {
  //
  // Generate a load, increment, and store right before the GEP.
  //
  LLVMContext & Context = Counter->getParent()->getContext();
  ConstantInt * One = ConstantInt::get (Type::getInt64Ty(Context), 1); 
  LoadInst * OldValue = new LoadInst (Counter, "count", SI);
  Instruction * NewValue = BinaryOperator::Create (BinaryOperator::Add,
                                                   OldValue,
                                                   One,
                                                   "count",
                                                   SI);
  new StoreInst (NewValue, Counter, SI);
  return;
}

//
// Method: runOnModule()
//
// Description:
//  Entry point for this pass.
//
bool
Dyncount::runOnModule (Module & M) {
  //
  // Create two global counters within the module.
  //
  TS = &getAnalysis<dsa::TypeSafety<TDDataStructures> >();
  ConstantInt * Zero = ConstantInt::get (Type::getInt64Ty(M.getContext()), 0); 
  GlobalVariable * Total = new GlobalVariable (M,
                                               Type::getInt64Ty(M.getContext()),
                                               false,
                                               GlobalValue::InternalLinkage,
                                               Zero,
                                               "Total");
  GlobalVariable * Safe = new GlobalVariable (M,
                                              Type::getInt64Ty(M.getContext()),
                                              false,
                                              GlobalValue::InternalLinkage,
                                              Zero,
                                              "Safe");

  for (Module::iterator F = M.begin(); F != M.end(); ++F){
    for (Function::iterator B = F->begin(), FE = F->end(); B != FE; ++B) {      
      for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE; I++) {
        if(LoadInst *LI = dyn_cast<LoadInst>(I)) {
          instrumentLoad(Total, LI);
          if(TS->isTypeSafe(LI->getOperand(0),LI->getParent()->getParent()))
            instrumentLoad(Safe, LI);

          // check if safe
        } else if(StoreInst *SI = dyn_cast<StoreInst>(I)) {
          instrumentStore(Total, SI);
          if(TS->isTypeSafe(SI->getOperand(1),SI->getParent()->getParent()))
            instrumentStore(Safe, SI);
          // check if safe
        }
      }
    }
  }

  //
  // Add a call to main() that will record the values on exit().
  //
  Function *MainFunc = M.getFunction("main") ? M.getFunction("main")
    : M.getFunction ("MAIN__");

  BasicBlock & BB = MainFunc->getEntryBlock();
  Constant * Setup = M.getOrInsertFunction ("DYN_COUNT_setup", Type::getVoidTy(M.getContext()), Total->getType(), Safe->getType(), NULL);
  std::vector<Value *> args;
  args.push_back (Total);
  args.push_back (Safe);
  CallInst::Create (Setup, args, "", BB.getFirstNonPHI());


  return true;
}

