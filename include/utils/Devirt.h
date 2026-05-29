//===- Devirt.h - Devirtualize indirect function calls via SVF ------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines an LLVM transform that converts indirect function calls
// into direct function calls, using SVF's Andersen call graph as the (sound)
// source of indirect-call targets.
//
//===----------------------------------------------------------------------===//

#ifndef SMACK_UTILS_DEVIRT_H
#define SMACK_UTILS_DEVIRT_H

#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/IPO.h"

#include <map>
#include <set>
#include <vector>

using namespace llvm;

namespace llvm {
//
// Class: Devirtualize
//
// Description:
//  This transform pass looks for indirect function calls and rewrites each one
//  whose targets SVF resolves *completely* into a direct dispatch (a "bounce"
//  function with an `if (fp == &target_i) call target_i(args)` chain ending in
//  `unreachable`). Callsites SVF cannot completely resolve are left untouched.
//
class DevirtualizeNewPM;
class Devirtualize : public ModulePass, public InstVisitor<Devirtualize> {
  friend class DevirtualizeNewPM;

private:
  // Access to the target data analysis pass.
  const DataLayout *TD;

  // Worklist of indirect call sites to consider.
  std::vector<CallBase *> Worklist;

  // A cache of indirect-call bounce functions that have been built already.
  std::map<const Function *, std::set<const Function *>> bounceCache;

protected:
  void makeDirectCall(CallBase *CS);
  Function *buildBounce(CallBase *CS, std::vector<const Function *> &Targets);
  const Function *findInCache(const CallBase *CS,
                              std::set<const Function *> &Targets);

public:
  static char ID;
  Devirtualize() : ModulePass(ID), TD(nullptr) {}

  virtual bool runOnModule(Module &M) override;

  // Devirt reuses the SVF analysis DSAWrapper builds, so it must run after it.
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override;

  // Visitor methods for analyzing instructions.
  void processCallSite(CallBase *CS);
  void visitCallInst(CallInst &CI) { processCallSite(&CI); }
  void visitInvokeInst(InvokeInst &II) { processCallSite(&II); }
};

class DevirtualizeNewPM : public PassInfoMixin<DevirtualizeNewPM> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);
  static StringRef name() { return "DevirtualizeNewPM"; }
};
} // namespace llvm

#endif // SMACK_UTILS_DEVIRT_H
