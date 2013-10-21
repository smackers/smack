//===-- AddressTakenAnalysis.h - Identify address Taken Values-------------===//
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
//===----------------------------------------------------------------------===//

#ifndef _ADDRESSTAKENANALYSIS_H
#define	_ADDRESSTAKENANALYSIS_H

#include "llvm/Pass.h"

#include <string>
#include <set>

namespace llvm {
class Function;
class Module;
class Instruction;

class AddressTakenAnalysis : public llvm::ModulePass {
  std::set<Function*> addressTakenFunctions;
public:
  static char ID;
  AddressTakenAnalysis() : ModulePass (ID) {}
  virtual ~AddressTakenAnalysis();

  bool runOnModule(llvm::Module&);

  virtual void getAnalysisUsage(llvm::AnalysisUsage &Info) const;

  bool hasAddressTaken(llvm::Function *);

};

}

#endif	/* _ADDRESSTAKENANALYSIS_H */

