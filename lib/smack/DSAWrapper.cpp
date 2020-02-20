//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE for details.
//
#include "smack/DSAWrapper.h"
#include "llvm/Support/FileSystem.h"
#include "smack/SmackOptions.h"

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

} // namespace smack
