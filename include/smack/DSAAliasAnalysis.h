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

#include "assistDS/DSNodeEquivs.h"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Module.h"

namespace smack {

using namespace std;

class MemcpyCollector : public llvm::InstVisitor<MemcpyCollector> {
private:
  llvm::DSNodeEquivs *nodeEqs;
  vector<const llvm::DSNode*> memcpys;
  
public:
  MemcpyCollector(llvm::DSNodeEquivs *neqs) : nodeEqs(neqs) { }

  void visitMemCpyInst(llvm::MemCpyInst& mci) {
    const llvm::EquivalenceClasses<const llvm::DSNode*> &eqs 
      = nodeEqs->getEquivalenceClasses();
    const llvm::DSNode *n1 = eqs.getLeaderValue(
      nodeEqs->getMemberForValue(mci.getOperand(0)) );
    const llvm::DSNode *n2 = eqs.getLeaderValue(
      nodeEqs->getMemberForValue(mci.getOperand(1)) );
    
    bool f1 = false, f2 = false;
    for (unsigned i=0; i<memcpys.size() && (!f1 || !f2); i++) {
      f1 = f1 || memcpys[i] == n1;
      f2 = f2 || memcpys[i] == n2;
    }

    if (!f1) memcpys.push_back(eqs.getLeaderValue(n1));
    if (!f2) memcpys.push_back(eqs.getLeaderValue(n2));
  }

  vector<const llvm::DSNode*> getMemcpys() {
    return memcpys;
  }
};
  
class DSAAliasAnalysis : public llvm::ModulePass, public llvm::AliasAnalysis {
private:
  llvm::TDDataStructures *TD;
  llvm::BUDataStructures *BU;
  llvm::DSNodeEquivs *nodeEqs;
  vector<const llvm::DSNode*> staticInits;
  vector<const llvm::DSNode*> memcpys;

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
    memcpys = collectMemcpys(M, new MemcpyCollector(nodeEqs));
    staticInits = collectStaticInits(M);

    return false;
  }

  llvm::DSNode *getNode(const llvm::Value* v);
  bool isAlloced(const llvm::Value* v);
  bool isExternal(const llvm::Value* v);
  bool isSingletonGlobal(const llvm::Value *V);

  virtual AliasResult alias(const Location &LocA, const Location &LocB);

private:
  bool isMemcpyd(const llvm::DSNode* n);
  bool isStaticInitd(const llvm::DSNode* n);
  vector<const llvm::DSNode*> collectMemcpys(llvm::Module &M, MemcpyCollector* mcc);
  vector<const llvm::DSNode*> collectStaticInits(llvm::Module &M);
  llvm::DSGraph *getGraphForValue(const llvm::Value *V);
  bool equivNodes(const llvm::DSNode* n1, const llvm::DSNode* n2);
  unsigned getOffset(const Location* l);
  bool disjoint(const Location* l1, const Location* l2);
};
}

#endif
