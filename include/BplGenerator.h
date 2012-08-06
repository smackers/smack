//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLGENERATOR_H
#define BPLGENERATOR_H

#include "BPLBlock.h"
#include "BPLInstVisitor.h"
#include "BPLModule.h"
#include "BPLPrintUtils.h"
#include "llvm/Function.h"
#include "llvm/InstrTypes.h"
#include "llvm/Pass.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CFG.h"
#include "llvm/Target/TargetData.h"
#include <map>
#include <vector>

using namespace llvm;

namespace smack {

class BplGenerator : public ModulePass {
private:
  BPLModule* bplModule;

public:
  static char ID; // Pass identification, replacement for typeid

  BplGenerator() : ModulePass(ID) {}
  virtual bool runOnModule(Module &m);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<TargetData>();
  }

  BPLModule* getBPLModule() const {
    return bplModule;
  }
};
}

#endif  /*BPLGENERATOR_H*/
