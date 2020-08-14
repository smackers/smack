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
#include "smack/SmackOptions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
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
  dataLayout = &M.getDataLayout();
  SD = &getAnalysis<seadsa::DsaAnalysis>().getDsaAnalysis();
  assert(SD->kind() == seadsa::GlobalAnalysisKind::CONTEXT_INSENSITIVE &&
         "Currently we only want the context-insensitive sea-dsa.");
  DG = &SD->getGraph(*M.begin());
  // Print the graph in dot format when debugging
  SDEBUG(DG->writeGraph("main.mem.dot"));
  collectStaticInits(M);
  collectMemOpds(M);
  countGlobalRefs();
  module = &M;
  return false;
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
        memOpds.insert(getNode(memcpyInst->getSource()));
        memOpds.insert(getNode(memcpyInst->getDest()));
      } else if (MemSetInst *memsetInst = dyn_cast<MemSetInst>(&*I))
        memOpds.insert(getNode(memsetInst->getDest()));
    }
  }
}

void DSAWrapper::countGlobalRefs() {
  for (auto &g : DG->globals()) {
    auto &cellRef = g.second;
    auto *node = cellRef->getNode();
    assert(node && "Global values should have DSNodes.");
    if (!globalRefCount.count(node))
      globalRefCount[node] = 1;
    else
      globalRefCount[node]++;
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

unsigned DSAWrapper::getPointedTypeSize(const Value *v) {
  if (llvm::PointerType *t = llvm::dyn_cast<llvm::PointerType>(v->getType())) {
    llvm::Type *pointedType = t->getElementType();
    if (pointedType->isSized())
      return dataLayout->getTypeStoreSize(pointedType);
    else
      return UINT_MAX;
  } else
    llvm_unreachable("Type should be pointer.");
}

unsigned DSAWrapper::getOffset(const Value *v) {
  if (!DG->hasCell(*v))
    return 0;
  return DG->getCell(*v).getOffset();
}

const seadsa::Node *DSAWrapper::getNode(const Value *v) {
  // For sea-dsa, a node is obtained by getting the cell first.
  // It's possible that a value doesn't have a cell, e.g., undef.
  if (!DG->hasCell(*v))
    return nullptr;
  auto node = DG->getCell(*v).getNode();
  assert(node && "Values should have nodes if they have cells.");
  return node;
}

bool DSAWrapper::isTypeSafe(const Value *v) {
  typedef std::unordered_map<unsigned, bool> FieldMap;
  typedef std::unordered_map<const seadsa::Node *, FieldMap> NodeMap;
  static NodeMap nodeMap;

  auto node = getNode(v);

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
        unsigned length =
            dataLayout->getTypeStoreSize(const_cast<llvm::Type *>(t));
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
