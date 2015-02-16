//===-- AddressTakenAnalysis.cpp - Address Taken Functions Finding Pass ---===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass helps find which functions are address taken in a module.
// Functions are considered to be address taken if they are either stored,
// or passed as arguments to functions.
// 
//
//===----------------------------------------------------------------------===//

#include "llvm/Pass.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/CallSite.h"

#include <fstream>
#include <set>

#include "dsa/AddressTakenAnalysis.h"

using namespace llvm;


AddressTakenAnalysis::~AddressTakenAnalysis() {}

static bool isAddressTaken(Value* V) {
  for (Value::const_use_iterator I = V->use_begin(), E = V->use_end(); I != E; ++I) {
    User *U = I->getUser();
    if(isa<StoreInst>(U))
      return true;
    if (!isa<CallInst>(U) && !isa<InvokeInst>(U)) {
      if(U->use_empty())
        continue;
      if(isa<GlobalAlias>(U)) {
        if(isAddressTaken(U))
          return true;
      } else {
        if (Constant *C = dyn_cast<Constant>(U)) {
          if (ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
            if (CE->getOpcode() == Instruction::BitCast) {
              return isAddressTaken(CE);
            }
          }
        }
        return true;
      }

      // FIXME: Can be more robust here for weak aliases that 
      // are never used
    } else {
      llvm::CallSite CS(cast<Instruction>(U));
      if (!CS.isCallee(&*I))
        return true;
    }
  }
  return false;
}

bool AddressTakenAnalysis::runOnModule(llvm::Module& M) {
  for (Module::iterator FI = M.begin(), FE = M.end(); FI != FE; ++FI){
    if(isAddressTaken(FI)) {
      addressTakenFunctions.insert(FI);
    }
  }

  return false;
}
bool AddressTakenAnalysis::hasAddressTaken(llvm::Function *F){
  return addressTakenFunctions.find(F) != addressTakenFunctions.end();
}

void AddressTakenAnalysis::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

char AddressTakenAnalysis::ID;
static RegisterPass<AddressTakenAnalysis> A("ata", "Identify Address Taken Functions");
