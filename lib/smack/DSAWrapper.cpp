//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE for details.
//
#include "smack/DSAWrapper.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"

#include "llvm/Support/FileSystem.h"

#include <set>
#include <unordered_map>

#define DEBUG_TYPE "dsa-wrapper"

namespace smack {

using namespace llvm;

char DSAWrapper::ID;
RegisterPass<DSAWrapper>
    DSAWrapperPass("dsa-wrapper",
                   "SMACK Data Structure Graph Based Alias Analysis Wrapper");

void DSAWrapper::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequiredTransitive<sea_dsa::DsaAnalysis>();
}

bool DSAWrapper::runOnModule(llvm::Module &M) {
  dataLayout = &M.getDataLayout();
  SD = &getAnalysis<sea_dsa::DsaAnalysis>().getDsaAnalysis();
  assert(SD->kind() == sea_dsa::GlobalAnalysisKind::CONTEXT_INSENSITIVE &&
         "Currently we only want the context-insensitive sea-dsa.");
  for (auto &f : M.functions()) {
    if (f.hasName() && SmackOptions::isEntryPoint(f.getName())) {
      DG = &SD->getGraph(f);
      break;
    }
  }

  collectStaticInits(M);
  collectMemCpyds(M);
  countGlobalRefs();
  module = &M;
  return false;
}

void DSAWrapper::collectStaticInits(llvm::Module &M) {
  for (GlobalVariable &GV : M.globals()) {
    if (GV.hasInitializer()) {
      if (auto *N = getNode(&GV)) {
        staticInits.insert(N);
      }
    }
  }
}

void DSAWrapper::collectMemCpyds(llvm::Module &M) {
  for (auto &f : M) {
    for (inst_iterator I = inst_begin(&f), E = inst_end(&f); I != E; ++I) {
      if (MemCpyInst *memcpyInst = dyn_cast<MemCpyInst>(&*I)) {
        auto srcNode = getNode(memcpyInst->getSource());
        auto destNode = getNode(memcpyInst->getDest());
        memCpyds.insert(srcNode);
        memCpyds.insert(destNode);
      }
      if (MemSetInst *memsetInst = dyn_cast<MemSetInst>(&*I)) {
        auto destNode = getNode(memsetInst->getDest());
        memCpyds.insert(destNode);
      }
    }
  }
}

void DSAWrapper::countGlobalRefs() {
  for (auto &g : DG->globals()) {
    auto &cellRef = g.second;
    auto *node = cellRef->getNode();
    if (node) {
      if (!globalRefCount.count(node))
        globalRefCount[node] = 1;
      else
        globalRefCount[node]++;
    }
  }
}

bool DSAWrapper::isStaticInitd(const sea_dsa::Node *n) {
  return staticInits.count(n) > 0;
}

bool DSAWrapper::isMemCpyd(const sea_dsa::Node *n) {
  return memCpyds.count(n) > 0;
}

bool DSAWrapper::isAlloced(const Value *v) {
  auto N = getNode(v);
  return N->isHeap() || N->isAlloca();
}

bool DSAWrapper::isExternal(const Value *v) { return getNode(v)->isExternal(); }

bool DSAWrapper::isRead(const Value *V) { return getNode(V)->isRead(); }

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

int DSAWrapper::getOffset(const Value *v) {
  if (DG->hasCell(*v)) {
    auto cell = DG->getCell(*v);
    auto node = cell.getNode();
    // Be consistent with the old implementation.
    if (node->isOffsetCollapsed())
      return -1;
    auto offset = cell.getOffset();
    assert(offset <= INT_MAX && "Cannot handle large offsets");
    return offset;
  }
  // Return 0 if we can't find the cell that `v` associates with.
  return 0;
}

const sea_dsa::Node *DSAWrapper::getNode(const Value *v) {
  // For sea-dsa, a node is obtained by getting the cell first.
  if (DG->hasCell(*v)) {
    auto node = DG->getCell(*v).getNode();
    assert(node && "DSNode should not be NULL.");
    return node;
  }
  llvm_unreachable("Values should have cells.");
}

bool DSAWrapper::isTypeSafe(const Value *v) {
  typedef std::unordered_map<unsigned, bool> FieldMap;
  typedef std::unordered_map<const sea_dsa::Node *, FieldMap> NodeMap;
  static NodeMap nodeMap;

  auto node = getNode(v);

  if (node->isOffsetCollapsed() || node->isExternal() || node->isIncomplete() ||
      node->isUnknown() || node->isIntToPtr() || node->isPtrToInt())
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
        bool overlap = false;
        unsigned next_offset = *oi;
        if (offset + fieldLength > next_offset) {
          // Overlaps; mark the current field and the next unsafe
          fieldMap[offset] = false;
          fieldMap[next_offset] = false;
          overlap = true;
        }
        if (!overlap)
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

unsigned DSAWrapper::getNumGlobals(const sea_dsa::Node *n) {
  if (globalRefCount.count(n))
    return globalRefCount[n];
  else
    return 0;
}

} // namespace smack
