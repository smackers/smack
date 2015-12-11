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
#include "llvm/Support/FileSystem.h"
#define DEBUG_TYPE "dsa-aa"

namespace smack {

using namespace llvm;

RegisterPass<DSAAliasAnalysis> A("ds-aa", "Data Structure Graph Based Alias Analysis");
RegisterAnalysisGroup<AliasAnalysis> B(A);
char DSAAliasAnalysis::ID = 0;

void DSAAliasAnalysis::printDSAGraphs(const char* Filename) {
  std::string EC;
  llvm::raw_fd_ostream F(Filename, EC, sys::fs::OpenFlags::F_None);
  TD->print(F, module);
  BU->print(F, module);
  TS->print(F, module);
}

std::vector<const llvm::DSNode*> DSAAliasAnalysis::collectMemcpys(
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


std::vector<const llvm::DSNode*> DSAAliasAnalysis::collectStaticInits(llvm::Module &M) {
  std::vector<const llvm::DSNode*> sis;

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

bool DSAAliasAnalysis::isComplicatedNode(const llvm::DSNode* N) {
  return
    N->isIntToPtrNode() || N->isPtrToIntNode() ||
    N->isExternalNode() || N->isUnknownNode();
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

bool DSAAliasAnalysis::isFieldDisjoint(const llvm::Value* V, const llvm::Function* F) {
  return TS->isFieldDisjoint(V, F);
}

bool DSAAliasAnalysis::isFieldDisjoint(const GlobalValue* V, unsigned offset) {
  return TS->isFieldDisjoint(V, offset);
}

DSGraph *DSAAliasAnalysis::getGraphForValue(const Value *V) {
  if (const Instruction *I = dyn_cast<Instruction>(V))
    return TD->getDSGraph(*I->getParent()->getParent());
  else if (const Argument *A = dyn_cast<Argument>(V))
    return TD->getDSGraph(*A->getParent());
  else if (const BasicBlock *BB = dyn_cast<BasicBlock>(V))
    return TD->getDSGraph(*BB->getParent());
  else if (isa<GlobalValue>(V))
    return TD->getGlobalsGraph();

  // XXX I know this looks bad, but it works for now
  for (auto U : V->users()) {
    return getGraphForValue(U);
  }

  llvm_unreachable("Unexpected value.");
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

// TODO: Should this return the node or its leader?
const DSNode *DSAAliasAnalysis::getNode(const Value* v) {
  const llvm::EquivalenceClasses<const llvm::DSNode*> &eqs
    = nodeEqs->getEquivalenceClasses();
  return eqs.getLeaderValue(nodeEqs->getMemberForValue(v));
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

unsigned DSAAliasAnalysis::getPointedTypeSize(const Value* v) {
  if (llvm::PointerType* t = llvm::dyn_cast<llvm::PointerType>(v->getType())) {
    llvm::Type* pointedType = t->getTypeAtIndex(0u);
    if (pointedType->isSized())
      return dataLayout->getTypeStoreSize(pointedType);
    else
      return UINT_MAX;
  } else
    llvm_unreachable("Type should be pointer.");
}

unsigned DSAAliasAnalysis::getOffset(const Value* v) {
  return getOffset(new Location(v));
}

AliasAnalysis::AliasResult DSAAliasAnalysis::alias(const Location &LocA, const Location &LocB) {

  if (LocA.Ptr == LocB.Ptr)
    return MustAlias;

  const DSNode *N1 = nodeEqs->getMemberForValue(LocA.Ptr);
  const DSNode *N2 = nodeEqs->getMemberForValue(LocB.Ptr);

  assert(N1 && "Expected non-null node.");
  assert(N2 && "Expected non-null node.");

  if (N1->isIncompleteNode() && N2->isIncompleteNode())
    goto surrender;

  if (isComplicatedNode(N1) && isComplicatedNode(N2))
    goto surrender;

  if (!equivNodes(N1,N2))
    return NoAlias;

  if (isMemcpyd(N1) || isMemcpyd(N2))
    goto surrender;

  if (isStaticInitd(N1) || isStaticInitd(N2))
    goto surrender;

  if (disjoint(&LocA,&LocB))
    return NoAlias;

  // FIXME: we could improve on this by checking the globals graph for aliased
  // global queries...
surrender:
  return AliasAnalysis::alias(LocA, LocB);
}

}
