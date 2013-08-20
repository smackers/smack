//===---------- TypeChecksOpt.h - Remove safe runtime type checks ---------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass removes type checks that are statically proven safe
//
//===----------------------------------------------------------------------===//

#ifndef TYPE_CHECKS_OPT_H
#define TYPE_CHECKS_OPT_H

#include "dsa/TypeSafety.h"

#include "llvm/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/DataLayout.h"
#include "llvm/Support/CallSite.h"

#include <list>

namespace llvm {

class Type;
class Value;

class TypeChecksOpt : public ModulePass {

private:

  // Analysis from other passes.
  dsa::TypeSafety<TDDataStructures> *TS;
  std::list<Instruction *> toDelete;

public:
  static char ID;
  TypeChecksOpt() : ModulePass(ID) {}
  virtual bool runOnModule(Module &M);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<dsa::TypeSafety<TDDataStructures> >();
  }

};

} // End llvm namespace

#endif
