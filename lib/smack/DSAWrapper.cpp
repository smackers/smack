//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE for details.
//
#include "smack/DSAWrapper.h"
#include "dsa/DataStructure.h"
#include "assistDS/DSNodeEquivs.h"
#include "dsa/DSGraph.h"
#include "dsa/TypeSafety.h"
#include "llvm/Support/FileSystem.h"

#define DEBUG_TYPE "dsa-wrapper"

namespace smack {

using namespace llvm;

char DSAWrapper::ID;
RegisterPass<DSAWrapper> DSAWrapperPass("dsa-wrapper",
  "SMACK Data Structure Graph Based Alias Analysis Wrapper");

void MemcpyCollector::visitMemCpyInst(llvm::MemCpyInst& mci) {
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

void DSAWrapper::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequiredTransitive<llvm::BUDataStructures>();
  AU.addRequiredTransitive<llvm::TDDataStructures>();
  AU.addRequiredTransitive<llvm::DSNodeEquivs>();
  AU.addRequired<dsa::TypeSafety<llvm::TDDataStructures> >();
}

bool DSAWrapper::runOnModule(llvm::Module &M) {
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

std::vector<const llvm::DSNode*> DSAWrapper::collectMemcpys(
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

std::vector<const llvm::DSNode*> DSAWrapper::collectStaticInits(llvm::Module &M) {
  std::vector<const llvm::DSNode*> sis;
  for (GlobalVariable &GV : M.globals()) {
    if (GV.hasInitializer()) {
      if (auto *N = getNode(&GV)) {
        sis.push_back(N);
      }
    }
  }
  return sis;
}

DSGraph *DSAWrapper::getGraphForValue(const Value *V) {
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

int DSAWrapper::getOffset(const MemoryLocation* l) {
  const DSGraph::ScalarMapTy& S = getGraphForValue(l->Ptr)->getScalarMap();
  DSGraph::ScalarMapTy::const_iterator I = S.find((const Value*)l->Ptr);
  if (I == S.end())
    return 0;
  if (I->second.getNode() && I->second.getNode()->isCollapsedNode())
    return -1;
  unsigned offset = I->second.getOffset();
  assert(offset <= INT_MAX && "Cannot handle large offsets");
  return (int) offset;
}

bool DSAWrapper::isMemcpyd(const llvm::DSNode* n) {
  const llvm::EquivalenceClasses<const llvm::DSNode*> &eqs
    = nodeEqs->getEquivalenceClasses();
  const llvm::DSNode* nn = eqs.getLeaderValue(n);
  for (unsigned i=0; i<memcpys.size(); i++)
    if (memcpys[i] == nn)
      return true;
  return false;
}

bool DSAWrapper::isStaticInitd(const llvm::DSNode* n) {
  const llvm::EquivalenceClasses<const llvm::DSNode*> &eqs
    = nodeEqs->getEquivalenceClasses();
  const llvm::DSNode* nn = eqs.getLeaderValue(n);
  for (unsigned i=0; i<staticInits.size(); i++)
    if (staticInits[i] == nn)
      return true;
  return false;
}

bool DSAWrapper::isFieldDisjoint(const llvm::Value* V, const llvm::Function* F) {
  return TS->isFieldDisjoint(V, F);
}

bool DSAWrapper::isFieldDisjoint(const GlobalValue* V, unsigned offset) {
  return TS->isFieldDisjoint(V, offset);
}

bool DSAWrapper::isRead(const Value* V) {
  const DSNode *N = getNode(V);
  return N && (N->isReadNode());
}

bool DSAWrapper::isAlloced(const Value* v) {
  const DSNode *N = getNode(v);
  return N && (N->isHeapNode() || N->isAllocaNode());
}

bool DSAWrapper::isExternal(const Value* v) {
  const DSNode *N = getNode(v);
  return N && N->isExternalNode();
}

bool DSAWrapper::isSingletonGlobal(const Value *V) {
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

unsigned DSAWrapper::getPointedTypeSize(const Value* v) {
  if (llvm::PointerType* t = llvm::dyn_cast<llvm::PointerType>(v->getType())) {
    llvm::Type* pointedType = t->getTypeAtIndex(0u);
    if (pointedType->isSized())
      return dataLayout->getTypeStoreSize(pointedType);
    else
      return UINT_MAX;
  } else
    llvm_unreachable("Type should be pointer.");
}

int DSAWrapper::getOffset(const Value* v) {
  return getOffset(new MemoryLocation(v));
}

// TODO: Should this return the node or its leader?
const DSNode *DSAWrapper::getNode(const Value* v) {
  const llvm::EquivalenceClasses<const llvm::DSNode*> &eqs
    = nodeEqs->getEquivalenceClasses();
  auto *N = nodeEqs->getMemberForValue(v);
  return N ? eqs.getLeaderValue(N) : nullptr;
}

void DSAWrapper::printDSAGraphs(const char* Filename) {
  std::error_code EC;
  llvm::raw_fd_ostream F(Filename, EC, sys::fs::OpenFlags::F_None);
  TD->print(F, module);
  BU->print(F, module);
  TS->print(F, module);
}

} // namespace smack
