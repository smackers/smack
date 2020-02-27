//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE for details.
//
#include "smack/DSAWrapper.h"
#include "llvm/Support/FileSystem.h"
#include "smack/SmackOptions.h"

#include <unordered_map>
#include <set>

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
  assert(SD->kind() == sea_dsa::GlobalAnalysisKind::CONTEXT_INSENSITIVE
         && "Currently we only want the context-insensitive sea-dsa.");
  for (auto& f : M.functions()) {
    if(f.hasName() && SmackOptions::isEntryPoint(f.getName())) {
      DG = &SD->getGraph(f);
      break;
    }
  }
  staticInits = collectStaticInits(M);
  module = &M;
  return false;
}

std::vector<const sea_dsa::Node *>
DSAWrapper::collectStaticInits(llvm::Module &M) {
  std::vector<const sea_dsa::Node *> sis;
  for (GlobalVariable &GV : M.globals()) {
    if (GV.hasInitializer()) {
      if (auto *N = getNode(&GV)) {
        sis.push_back(N);
      }
    }
  }
  return sis;
}

bool DSAWrapper::isStaticInitd(const sea_dsa::Node *n) {
  for (unsigned i = 0; i < staticInits.size(); i++)
    if (staticInits[i] == n)
      return true;
  return false;
}

bool DSAWrapper::isRead(const Value *V) {
  auto N = getNode(V);
  return N && (N->isRead());
}

bool DSAWrapper::isAlloced(const Value *v) {
  auto N = getNode(v);
  return N && (N->isHeap() || N->isAlloca());
}

bool DSAWrapper::isExternal(const Value *v) {
  auto N = getNode(v);
  return N && N->isExternal();
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

int DSAWrapper::getOffset(const Value *v) {
  if (DG->hasCell(*v)) {
    auto cell = DG->getCell(*v);
    auto node = cell.getNode();
    // Be consistent with the old implementation.
    if (node && node->isOffsetCollapsed())
      return -1;
    auto offset = cell.getOffset();
    errs() << "working on offset: " << offset << "\n";
    assert(offset <= INT_MAX && "Cannot handle large offsets");
    return offset;
  }
  // Return 0 if we can't find the cell that `v` associates with.
  return 0;
}

const sea_dsa::Node *DSAWrapper::getNode(const Value *v) {
  // For sea-dsa, a node is obtained by getting the cell first.
  if (DG->hasCell(*v))
    return DG->getCell(*v).getNode();
  return nullptr;
}

void DSAWrapper::printDSAGraphs(const char *Filename) {
  std::error_code EC;
  llvm::raw_fd_ostream F(Filename, EC, sys::fs::OpenFlags::F_None);
  // TODO: print the ds graph
}

bool DSAWrapper::isTypeSafe(const Value *v) {
  typedef std::unordered_map<unsigned, bool> FieldMap;
  typedef std::unordered_map<const sea_dsa::Node*, FieldMap> NodeMap;
  static NodeMap nodeMap;

  auto node = getNode(v);

  if (!node
      || node->isOffsetCollapsed() || node->isExternal() || node->isIncomplete()
      || node->isUnknown() || node->isIntToPtr() || node->isPtrToInt())
    // We consider it type-unsafe to be safe for these cases
    return false;

  if (!nodeMap.count(node)) {
    // Shaobo: iterate all the fields of a node to find out
    // the type-safety of each field. Then, we cache the results.


    FieldMap fieldMap;
    auto &types = node->types();
    std::set<unsigned> offsets;

    for (auto& t : types) {
      errs() << "inserting offset: " << t.first << "\n";
      offsets.insert(t.first);
    }


    auto offsetIterator = offsets.begin();

    while (true) {
      if (offsetIterator == offsets.end())
        // We have reached the last field and exit the loop
        break;

      unsigned offset = *offsetIterator;

      errs() << "working on offset: " << offset << "\n";
      auto& typeSet = types.find(offset)->second;

      auto ti = typeSet.begin();
      if (++ti != typeSet.end())
        // If there are multiple access types, then it's trivially type-unsafe.
        fieldMap[offset] = false;

      unsigned fieldLength = 0;
      for (auto &t : typeSet) {
        unsigned length = dataLayout->getTypeStoreSize(const_cast<llvm::Type*>(t));
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
  errs() << "value is " << *v << "\n";
  errs() << "offset is " << offset << "\n";
  //assert(nodeMap[node].count(offset) > 0 && "We should have this info.");
  if (nodeMap[node].count(offset))
    return nodeMap[node][offset];
  else
    return false;

  
}

} // namespace smack
