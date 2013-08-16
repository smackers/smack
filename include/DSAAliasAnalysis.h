//===- DataStructureAA.cpp - Data Structure Based Alias Analysis ----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass uses the top-down data structure graphs to implement a simple
// context sensitive alias analysis.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_DATA_STRUCTURE_AA_H
#define LLVM_ANALYSIS_DATA_STRUCTURE_AA_H

#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Module.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"

#include "assistDS/DSNodeEquivs.h"

namespace smack {
  
class DSAAliasAnalysis : public llvm::ModulePass, public llvm::AliasAnalysis {
private:
  llvm::TDDataStructures *TD;
  llvm::BUDataStructures *BU;  
  llvm::DSNodeEquivs *nodeEqs;

public:
  static char ID;
  DSAAliasAnalysis() : ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    llvm::AliasAnalysis::getAnalysisUsage(AU);
    AU.setPreservesAll();
    AU.addRequiredTransitive<llvm::TDDataStructures>();
    AU.addRequiredTransitive<llvm::BUDataStructures>();
    AU.addRequiredTransitive<llvm::DSNodeEquivs>();
  }

  virtual bool runOnModule(llvm::Module &M) {
    InitializeAliasAnalysis(this);
    TD = &getAnalysis<llvm::TDDataStructures>();
    BU = &getAnalysis<llvm::BUDataStructures>();
    nodeEqs = &getAnalysis<llvm::DSNodeEquivs>();
    return false;
  }

  virtual AliasResult alias(const Location &LocA, const Location &LocB);
  
private:
  llvm::DSGraph *getGraphForValue(const llvm::Value *V);
  bool equivNodes(const llvm::DSNode* n1, const llvm::DSNode* n2);
  unsigned getOffset(const Location* l);
  bool disjoint(const Location* l1, const Location* l2);
};
}

#endif
