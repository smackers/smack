//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE for details.
//
#include "smack/DSAWrapper.h"
#include "llvm/Support/FileSystem.h"

#define DEBUG_TYPE "dsa-wrapper"

namespace smack {

using namespace llvm;

char DSAWrapper::ID;
RegisterPass<DSAWrapper> DSAWrapperPass("dsa-wrapper",
  "SMACK Data Structure Graph Based Alias Analysis Wrapper");

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

unsigned DSAWrapper::getOffset(const MemoryLocation* l) {
  const DSGraph::ScalarMapTy& S = getGraphForValue(l->Ptr)->getScalarMap();
  DSGraph::ScalarMapTy::const_iterator I = S.find((const Value*)l->Ptr);
  return (I == S.end()) ? 0 : (I->second.getOffset());
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

unsigned DSAWrapper::getOffset(const Value* v) {
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
