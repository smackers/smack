//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE for details.
//
#ifndef DSAWRAPPER_H
#define DSAWRAPPER_H

#include "assistDS/DSNodeEquivs.h"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "dsa/TypeSafety.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Module.h"
#include <unordered_set>

namespace smack {

class MemcpyCollector : public llvm::InstVisitor<MemcpyCollector> {
private:
  llvm::DSNodeEquivs *nodeEqs;
  std::vector<const llvm::DSNode*> memcpys;

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

  std::vector<const llvm::DSNode*> getMemcpys() {
    return memcpys;
  }
};

class DSAWrapper : public llvm::ModulePass {
private:
  llvm::Module *module;
  llvm::TDDataStructures *TD;
  llvm::BUDataStructures *BU;
  llvm::DSNodeEquivs *nodeEqs;
  dsa::TypeSafety<llvm::TDDataStructures> *TS;
  std::vector<const llvm::DSNode*> staticInits;
  std::vector<const llvm::DSNode*> memcpys;
  std::unordered_set<const llvm::DSNode*> intConversions;
  const DataLayout* dataLayout;

  std::vector<const llvm::DSNode*> collectMemcpys(llvm::Module &M, MemcpyCollector* mcc);
  std::vector<const llvm::DSNode*> collectStaticInits(llvm::Module &M);
  llvm::DSGraph *getGraphForValue(const llvm::Value *V);
  unsigned getOffset(const MemoryLocation* l);

public:
  static char ID;
  DSAWrapper() : ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequiredTransitive<llvm::BUDataStructures>();
    AU.addRequiredTransitive<llvm::TDDataStructures>();
    AU.addRequiredTransitive<llvm::DSNodeEquivs>();
    AU.addRequired<dsa::TypeSafety<llvm::TDDataStructures> >();
  }

  virtual bool runOnModule(llvm::Module &M) {
    dataLayout = &M.getDataLayout();
    TD = &getAnalysis<llvm::TDDataStructures>();
    BU = &getAnalysis<llvm::BUDataStructures>();
    nodeEqs = &getAnalysis<llvm::DSNodeEquivs>();
    TS = &getAnalysis<dsa::TypeSafety<llvm::TDDataStructures> >();
    memcpys = collectMemcpys(M, new MemcpyCollector(nodeEqs));
    staticInits = collectStaticInits(M);
    module = &M;
    return false;
  }

  bool isMemcpyd(const llvm::DSNode* n);
  bool isStaticInitd(const llvm::DSNode* n);
  bool isFieldDisjoint(const llvm::Value* V, const llvm::Function* F);
  bool isFieldDisjoint(const GlobalValue* V, unsigned offset);
  bool isRead(const llvm::Value* V);
  bool isAlloced(const llvm::Value* v);
  bool isExternal(const llvm::Value* v);
  bool isSingletonGlobal(const llvm::Value *V);
  unsigned getPointedTypeSize(const Value* v);
  unsigned getOffset(const Value* v);
  const llvm::DSNode *getNode(const llvm::Value* v);
  void printDSAGraphs(const char* Filename);
};
}

#endif // DSAWRAPPER_H
