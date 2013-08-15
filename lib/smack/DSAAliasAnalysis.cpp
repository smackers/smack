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

#ifdef ENABLE_DSA

#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Module.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "DSAAliasAnalysis.h"

namespace smack {

using namespace llvm;

RegisterPass<DSAAliasAnalysis> A("ds-aa", "Data Structure Graph Based Alias Analysis");
RegisterAnalysisGroup<AliasAnalysis> B(A);
char DSAAliasAnalysis::ID = 0;

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

bool DSAAliasAnalysis::equivNodes(const Location* l1, const Location* l2) {
  return equivNodes(
    nodeEqs->getMemberForValue(l1->Ptr), 
    nodeEqs->getMemberForValue(l2->Ptr) );
}

bool DSAAliasAnalysis::isComplete(const Location* l) {
  return nodeEqs->getMemberForValue(l->Ptr)->isCompleteNode();
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
    
    if (disjoint(&LocA,&LocB))
      return NoAlias;
  }
  
  // if (isComplete(&LocA) || isComplete(&LocB)) {
  // 
  //   if (!equivNodes(&LocA,&LocB))
  //     return NoAlias;
  // 
  //   if (!overlappingNodes(&LocA,&LocB))
  //     return NoAlias;
  // }

  //   DSGraph *G1 = getGraphForValue(LocA.Ptr);
  // DSGraph *G2 = getGraphForValue(LocB.Ptr);
  // 
  // const DSGraph::ScalarMapTy &GSM1 = G1->getScalarMap();
  // DSGraph::ScalarMapTy::const_iterator I = GSM1.find((Value*)LocA.Ptr);
  // if (I == GSM1.end()) return NoAlias;
  // 
  // const DSGraph::ScalarMapTy &GSM2 = G2->getScalarMap();
  // DSGraph::ScalarMapTy::const_iterator J = GSM2.find((Value*)LocB.Ptr);
  // if (J == GSM2.end()) return NoAlias;
  // 
  // // DSNode  *N1 = I->second.getNode(),  *N2 = J->second.getNode();
  // 
  // const DSNode *N1 = nodeEqs->getMemberForValue(LocA.Ptr);
  // const DSNode *N2 = nodeEqs->getMemberForValue(LocB.Ptr);
  // 
  // unsigned O1 = I->second.getOffset(), O2 = J->second.getOffset();
  // if (N1 == 0 || N2 == 0)
  //   // Can't tell whether anything aliases null.
  //   return AliasAnalysis::alias(LocA, LocB);
  // 
  // // We can only make a judgment if one of the nodes is complete.
  // if (N1->isCompleteNode() || N2->isCompleteNode()) {
  //   
  //   if (!equivNodes(N1,N2))
  //     return NoAlias;   // Completely different nodes.
  // 
  //   // See if they point to different offsets...  if so, we may be able to
  //   // determine that they do not alias...
  //   if (O1 < O2 && O1+LocA.Size <= O2)
  //     return NoAlias;
  // 
  //   if (O2 < O1 && O2+LocB.Size <= O1)
  //     return NoAlias;
  // }
  
  // FIXME: we could improve on this by checking the globals graph for aliased
  // global queries...
  return AliasAnalysis::alias(LocA, LocB);
}

}
#endif
