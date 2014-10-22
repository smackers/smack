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

#include "smack/DSAAliasAnalysis.h"

namespace smack {

using namespace llvm;

RegisterPass<DSAAliasAnalysis> A("ds-aa", "Data Structure Graph Based Alias Analysis");
RegisterAnalysisGroup<AliasAnalysis> B(A);
char DSAAliasAnalysis::ID = 0;

vector<const llvm::DSNode*> DSAAliasAnalysis::collectMemcpys(
    llvm::Module &M, MemcpyCollector *mcc) {

  for (llvm::Module::iterator func = M.begin(), e = M.end();
       func != e; ++func) {
         
    for (llvm::Function::iterator block = func->begin(); 
        block != func->end(); ++block) {
        
      mcc->visit(*block);
    }
  }
  return mcc->getMemcpys();
}


vector<const llvm::DSNode*> DSAAliasAnalysis::collectStaticInits(llvm::Module &M) {
  vector<const llvm::DSNode*> sis;

  const llvm::EquivalenceClasses<const llvm::DSNode*> &eqs 
    = nodeEqs->getEquivalenceClasses();
  for (llvm::Module::const_global_iterator
       g = M.global_begin(), e = M.global_end(); g != e; ++g) {
    if (g->hasInitializer()) {
      sis.push_back(eqs.getLeaderValue(nodeEqs->getMemberForValue(g)));
    }
  }
  return sis;
}

bool DSAAliasAnalysis::isMemcpyd(const llvm::DSNode* n) {
  const llvm::EquivalenceClasses<const llvm::DSNode*> &eqs 
    = nodeEqs->getEquivalenceClasses();
  const llvm::DSNode* nn = eqs.getLeaderValue(n);
  for (unsigned i=0; i<memcpys.size(); i++)
    if (memcpys[i] == nn)
      return true;
  return false;
}

bool DSAAliasAnalysis::isStaticInitd(const llvm::DSNode* n) {
  const llvm::EquivalenceClasses<const llvm::DSNode*> &eqs 
    = nodeEqs->getEquivalenceClasses();
  const llvm::DSNode* nn = eqs.getLeaderValue(n);
  for (unsigned i=0; i<staticInits.size(); i++)
    if (staticInits[i] == nn)
      return true;
  return false;
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

DSNode *DSAAliasAnalysis::getNode(const Value* v) {
  return getGraphForValue(v)->getNodeForValue(v).getNode();
}

bool DSAAliasAnalysis::isAlloced(const Value* v) {
  const DSNode *N = getNode(v);
  return N && (N->isHeapNode() || N->isAllocaNode());
}

bool DSAAliasAnalysis::isExternal(const Value* v) {
  const DSNode *N = getNode(v);
  return N && N->isExternalNode();
}

bool DSAAliasAnalysis::isSingletonGlobal(const Value *V) {
  const DSNode *N = getNode(V);
  if (!N || !N->isGlobalNode() || N->numGlobals() > 1)
    return false;

  // Ensure this node has a unique scalar type... (?)
  DSNode::const_type_iterator TSi = N->type_begin();
  if (TSi == N->type_end()) return false;
  svset<Type*>::const_iterator Ti = TSi->second->begin();
  if (Ti == TSi->second->end()) return false;
  const Type* T = *Ti;
  while (T->isPointerTy()) T = T->getPointerElementType();
  if (!T->isSingleValueType()) return false;
  ++Ti;
  if (Ti != TSi->second->end()) return false;
  ++TSi;
  if (TSi != N->type_end()) return false;

  // Ensure this node is in its own class... (?)
  const EquivalenceClasses<const DSNode*> &Cs = nodeEqs->getEquivalenceClasses();
  EquivalenceClasses<const DSNode*>::iterator C = Cs.findValue(N);
  assert(C != Cs.end() && "Did not find value.");
  EquivalenceClasses<const DSNode*>::member_iterator I = Cs.member_begin(C);
  if (I == Cs.member_end())
    return false;
  ++I;
  if (I != Cs.member_end())
    return false;

  return true;
}

AliasAnalysis::AliasResult DSAAliasAnalysis::alias(const Location &LocA, const Location &LocB) {

  if (LocA.Ptr == LocB.Ptr)
    return MustAlias;

  const DSNode *N1 = nodeEqs->getMemberForValue(LocA.Ptr);
  const DSNode *N2 = nodeEqs->getMemberForValue(LocB.Ptr);

  assert(N1 && "Expected non-null node.");
  assert(N2 && "Expected non-null node.");

  if ((N1->isCompleteNode() || N2->isCompleteNode()) &&
      !(N1->isExternalNode() && N2->isExternalNode()) &&
      !(N1->isUnknownNode() || N2->isUnknownNode())) {

    if (!equivNodes(N1,N2))
      return NoAlias;
    
    if (!isMemcpyd(N1) && !isMemcpyd(N2) 
      && !isStaticInitd(N1) && !isStaticInitd(N2) 
      && disjoint(&LocA,&LocB))
      return NoAlias;
  }
  
  // FIXME: we could improve on this by checking the globals graph for aliased
  // global queries...
  return AliasAnalysis::alias(LocA, LocB);
}

}
