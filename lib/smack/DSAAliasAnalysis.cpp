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

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Module.h"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "smack/DSAAliasAnalysis.h"

namespace smack {

using namespace llvm;

RegisterPass<DSAAliasAnalysis> A("ds-aa", "Data Structure Graph Based Alias Analysis");
RegisterAnalysisGroup<AliasAnalysis> B(A);
char DSAAliasAnalysis::ID = 0;

void DSAAliasAnalysis::collectMemcpys(llvm::Module &M) {
  for (llvm::Module::iterator func = M.begin(), e = M.end();
       func != e; ++func) {
         
    for (llvm::Function::iterator block = func->begin(); 
        block != func->end(); ++block) {
        
      memcpys->visit(*block);
    }
  }
}

DSGraph *DSAAliasAnalysis::getGraphForValue(const Value *V) {
  if (const Instruction *I = dyn_cast<Instruction>(V))
    return TD->getDSGraph(*I->getParent()->getParent());
  else if (const Argument *A = dyn_cast<Argument>(V))
    return TD->getDSGraph(*A->getParent());
  else if (const BasicBlock *BB = dyn_cast<BasicBlock>(V))
    return TD->getDSGraph(*BB->getParent());
  return TD->getGlobalsGraph();
}

bool DSAAliasAnalysis::equivNodes(const DSNode* n1, const DSNode* n2) {
  const EquivalenceClasses<const DSNode*> &eqs 
    = nodeEqs->getEquivalenceClasses();
  
  return eqs.getLeaderValue(n1) == eqs.getLeaderValue(n2);
}

unsigned DSAAliasAnalysis::getOffset(const Location* l) {
  const DSGraph::ScalarMapTy& S = getGraphForValue(l->Ptr)->getScalarMap();
  DSGraph::ScalarMapTy::const_iterator I = S.find((Value*)l->Ptr);
  return (I == S.end()) ? 0 : (I->second.getOffset());
}

bool DSAAliasAnalysis::disjoint(const Location* l1, const Location* l2) {
  unsigned o1 = getOffset(l1);
  unsigned o2 = getOffset(l2);
  return 
    (o1 < o2 && o1 + l1->Size <= o2)
    || (o2 < o1 && o2 + l2->Size <= o1);
}

AliasAnalysis::AliasResult DSAAliasAnalysis::alias(const Location &LocA, const Location &LocB) {

  if (LocA.Ptr == LocB.Ptr) 
    return MustAlias;

  const DSNode *N1 = nodeEqs->getMemberForValue(LocA.Ptr);
  const DSNode *N2 = nodeEqs->getMemberForValue(LocB.Ptr);
  
  if (N1->isCompleteNode() || N2->isCompleteNode()) {
    if (!equivNodes(N1,N2))
      return NoAlias;
    
    if (!memcpys->has(N1) && !memcpys->has(N2) && disjoint(&LocA,&LocB))
      return NoAlias;
  }
  
  // FIXME: we could improve on this by checking the globals graph for aliased
  // global queries...
  return AliasAnalysis::alias(LocA, LocB);
}

}
