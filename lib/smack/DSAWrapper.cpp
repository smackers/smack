//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE for details.
//
#include "smack/DSAWrapper.h"
#include "seadsa/InitializePasses.hh"
#include "smack/Debug.h"
#include "smack/InitializePasses.h"
#include "smack/LlvmCompat.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/FileSystem.h"

#include <set>
#include <unordered_map>

#define DEBUG_TYPE "smack-dsa-wrapper"

namespace smack {

using namespace llvm;

void DSAWrapper::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequiredTransitive<seadsa::DsaAnalysis>();
}

bool DSAWrapper::runOnModule(llvm::Module &M) {
  module = &M;
  dataLayout = &M.getDataLayout();
  SD = &getAnalysis<seadsa::DsaAnalysis>().getDsaAnalysis();
  DG = nullptr;
  for (auto &F : M) {
    if (SD->hasGraph(F)) {
      DG = &SD->getGraph(F);
      break;
    }
  }
  // Print the graph in dot format when debugging
  SDEBUG(if (DG) DG->writeGraph("main.mem.dot"));
  collectStaticInits(M);
  collectMemOpds(M);
  countGlobalRefs();
  return false;
}

seadsa::Graph *DSAWrapper::getGraphForValue(const llvm::Value *v) {
  return const_cast<seadsa::Graph *>(
      static_cast<const DSAWrapper *>(this)->getGraphForValue(v));
}

const seadsa::Graph *DSAWrapper::getGraphForValue(const llvm::Value *v) const {
  if (!SD || !v)
    return nullptr;

  if (SD->kind() == seadsa::GlobalAnalysisKind::CONTEXT_INSENSITIVE ||
      SD->kind() == seadsa::GlobalAnalysisKind::FLAT_MEMORY)
    return DG;

  if (auto *I = dyn_cast<Instruction>(v)) {
    auto *F = I->getFunction();
    if (F && SD->hasGraph(*F))
      return &SD->getGraph(*F);
  } else if (auto *A = dyn_cast<Argument>(v)) {
    auto *F = A->getParent();
    if (F && SD->hasGraph(*F))
      return &SD->getGraph(*F);
  } else if (auto *BB = dyn_cast<BasicBlock>(v)) {
    auto *F = BB->getParent();
    if (F && SD->hasGraph(*F))
      return &SD->getGraph(*F);
  }

  if (module) {
    for (auto &F : *module) {
      if (!SD->hasGraph(F))
        continue;
      auto &G = SD->getGraph(F);
      if (G.hasCell(*v))
        return &G;
    }
  }

  return DG;
}

void DSAWrapper::collectStaticInits(llvm::Module &M) {
  for (GlobalVariable &GV : M.globals()) {
    if (GV.hasInitializer()) {
      if (auto *N = getNode(&GV)) {
        assert(N && "Global values should have nodes.");
        staticInits.insert(N);
      }
    }
  }
}

void DSAWrapper::collectMemOpds(llvm::Module &M) {
  for (auto &f : M) {
    for (inst_iterator I = inst_begin(&f), E = inst_end(&f); I != E; ++I) {
      if (MemCpyInst *memcpyInst = dyn_cast<MemCpyInst>(&*I)) {
        if (auto *N = getNode(memcpyInst->getSource()))
          memOpds.insert(N);
        if (auto *N = getNode(memcpyInst->getDest()))
          memOpds.insert(N);
      } else if (MemSetInst *memsetInst = dyn_cast<MemSetInst>(&*I)) {
        if (auto *N = getNode(memsetInst->getDest()))
          memOpds.insert(N);
      }
    }
  }
}

void DSAWrapper::countGlobalRefs() {
  globalRefCount.clear();
  std::unordered_set<const seadsa::Graph *> seen;
  if (module) {
    for (auto &F : *module) {
      if (!SD->hasGraph(F))
        continue;
      auto *G = &SD->getGraph(F);
      if (!seen.insert(G).second)
        continue;
      for (auto &g : G->globals()) {
        auto &cellRef = g.second;
        auto *node = cellRef->getNode();
        assert(node && "Global values should have DSNodes.");
        globalRefCount[node]++;
      }
    }
  }
  if (globalRefCount.empty() && DG) {
    for (auto &g : DG->globals()) {
      auto &cellRef = g.second;
      auto *node = cellRef->getNode();
      assert(node && "Global values should have DSNodes.");
      globalRefCount[node]++;
    }
  }
}

bool DSAWrapper::isStaticInitd(const seadsa::Node *n) {
  return staticInits.count(n) > 0;
}

bool DSAWrapper::isMemOpd(const seadsa::Node *n) {
  return memOpds.count(n) > 0;
}

bool DSAWrapper::isRead(const Value *V) {
  auto node = getNode(V);
  assert(node && "Global values should have nodes.");
  return node->isRead();
}

const Type *DSAWrapper::getPointedType(const Value *v) {
  if (!v->getType()->isPointerTy())
    llvm_unreachable("Type should be pointer.");

  if (auto *T = legacyPointerElementType(v))
    return T;

  if (auto *AI = dyn_cast<AllocaInst>(v))
    return AI->getAllocatedType();

  if (auto *GV = dyn_cast<GlobalVariable>(v))
    return GV->getValueType();

  if (auto *GEP = dyn_cast<GetElementPtrInst>(v))
    return GEP->getResultElementType();

  if (auto *GEP = dyn_cast<GEPOperator>(v))
    return GEP->getResultElementType();

  auto *node = getNode(v);
  if (!node)
    return nullptr;

  const auto &types = node->types();
  auto offset = getOffset(v);
  auto it = types.find(offset);
  if (it == types.end() || it->second.begin() == it->second.end())
    return nullptr;

  const Type *best = nullptr;
  uint64_t bestSize = 0;
  for (auto *T : it->second) {
    if (!T || !T->isSized())
      continue;
    uint64_t size = fixedTypeStoreSize(*dataLayout, T);
    if (!best || size > bestSize) {
      best = T;
      bestSize = size;
    }
  }
  return best;
}

unsigned DSAWrapper::getPointedTypeSize(const Value *v) {
  const Type *pointedType = getPointedType(v);
  if (pointedType && pointedType->isSized())
    return fixedTypeStoreSize(*dataLayout, pointedType);
  return UINT_MAX;
}

unsigned DSAWrapper::getOffset(const Value *v) {
  auto *G = getGraphForValue(v);
  if (!G || !G->hasCell(*v))
    return 0;
  return G->getCell(*v).getOffset();
}

const seadsa::Node *DSAWrapper::getNode(const Value *v) {
  // For sea-dsa, a node is obtained by getting the cell first.
  // It's possible that a value doesn't have a cell, e.g., undef.
  auto *G = getGraphForValue(v);
  if (!G || !G->hasCell(*v))
    return nullptr;
  auto node = G->getCell(*v).getNode();
  assert(node && "Values should have nodes if they have cells.");
  return node;
}

bool DSAWrapper::isTypeSafe(const Value *v) {
  typedef std::unordered_map<unsigned, bool> FieldMap;
  typedef std::unordered_map<const seadsa::Node *, FieldMap> NodeMap;
  static NodeMap nodeMap;

  auto node = getNode(v);
  if (!node)
    return false;

  if (node->isOffsetCollapsed() || node->isExternal() || node->isIncomplete() ||
      node->isUnknown() || node->isIntToPtr() || node->isPtrToInt() ||
      isMemOpd(node))
    // We consider it type-unsafe to be safe for these cases
    return false;

  if (!nodeMap.count(node)) {
    // Iterate all the fields of a node to find out
    // the type-safety of each field. Then, we cache the results.
    FieldMap fieldMap;
    auto &types = node->types();
    std::set<unsigned> offsets;

    for (auto &t : types)
      offsets.insert(t.first);

    auto offsetIterator = offsets.begin();

    while (true) {
      if (offsetIterator == offsets.end())
        // We have reached the last field and exit the loop
        break;

      unsigned offset = *offsetIterator;

      auto &typeSet = types.find(offset)->second;

      auto ti = typeSet.begin();
      if (++ti != typeSet.end())
        // If there are multiple access types, then it's trivially type-unsafe.
        fieldMap[offset] = false;

      // Get the maximum length
      unsigned fieldLength = 0;
      for (auto &t : typeSet) {
        // TODO: fix the const_cast
        unsigned length = fixedTypeStoreSize(*dataLayout, t);
        if (length > fieldLength)
          fieldLength = length;
      }

      // Check if the current field overlaps with the next *fields*
      for (auto oi = ++offsetIterator; oi != offsets.end(); ++oi) {
        unsigned next_offset = *oi;
        if (offset + fieldLength > next_offset) {
          // Overlaps; mark the current field and the next unsafe
          fieldMap[offset] = false;
          fieldMap[next_offset] = false;
        } else
          // If the current field doesn't overlap with the next one,
          // it certainly won't overlap with the rest.
          break;
      }

      if (!fieldMap.count(offset))
        fieldMap[offset] = true;
    }

    nodeMap[node] = fieldMap;
  }

  auto offset = getOffset(v);
  if (nodeMap[node].count(offset))
    return nodeMap[node][offset];
  else
    // Chances to hit this branch are when we visit memcpy/memset
    // pointer operands.
    return false;
}

unsigned DSAWrapper::getNumGlobals(const seadsa::Node *n) {
  if (globalRefCount.count(n))
    return globalRefCount[n];
  else
    return 0;
}

std::string DSAWrapper::analysisKindName() const {
  if (!SD)
    return "unknown";
  switch (SD->kind()) {
  case seadsa::GlobalAnalysisKind::CONTEXT_INSENSITIVE:
    return "ci";
  case seadsa::GlobalAnalysisKind::CONTEXT_SENSITIVE:
    return "cs";
  case seadsa::GlobalAnalysisKind::BUTD_CONTEXT_SENSITIVE:
    return "butd-cs";
  case seadsa::GlobalAnalysisKind::BU:
    return "bu";
  case seadsa::GlobalAnalysisKind::FLAT_MEMORY:
    return "flat";
  }
  return "unknown";
}

} // namespace smack

char smack::DSAWrapper::ID = 0;

using namespace smack;
using namespace seadsa;
INITIALIZE_PASS_BEGIN(DSAWrapper, "smack-dsa-wrapper",
                      "SMACK Data Structure Graph Based Alias Analysis Wrapper",
                      false, false)
INITIALIZE_PASS_DEPENDENCY(DsaAnalysis)
INITIALIZE_PASS_END(DSAWrapper, "smack-dsa-wrapper",
                    "SMACK Data Structure Graph Based Alias Analysis Wrapper",
                    false, false)
