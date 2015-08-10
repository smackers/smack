//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REGIONS_H
#define REGIONS_H

#include "smack/DSAAliasAnalysis.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InstVisitor.h"
#include <set>

namespace smack {

using namespace std;

struct Region {
  set<const llvm::Value*> representatives;
  bool isAllocated;
  bool isSingletonGlobal;
  Region(const llvm::Value* r, bool a, bool s) :
    isAllocated(a), isSingletonGlobal(s) {
    representatives.insert(r);
  }
  void unifyWith(Region r) {
    representatives.insert(r.representatives.begin(), r.representatives.end());
    isAllocated = isAllocated || r.isAllocated;
    assert(isSingletonGlobal == r.isSingletonGlobal);
  }
};

class RegionManager : public llvm::InstVisitor<RegionManager> {
private:
  const llvm::DataLayout* targetData;
  DSAAliasAnalysis* aliasAnalysis;
  vector<Region> memoryRegions;

public:
  RegionManager(const DataLayout* L, DSAAliasAnalysis* aa) : targetData(L), aliasAnalysis(aa) {}
  unsigned size();
  Region getRegion(unsigned idx);
  unsigned getRegion(const llvm::Value* v);
  void visitModule(llvm::Module& M) {
    for (llvm::Module::const_global_iterator
         G = M.global_begin(), E = M.global_end(); G != E; ++G)
      getRegion(G);
  }
  void visitAllocaInst(llvm::AllocaInst& I) {
    getRegion(&I);
  }
  void visitLoadInst(llvm::LoadInst& I) {
    getRegion(I.getPointerOperand());
  }
  void visitStoreInst(llvm::StoreInst& I) {
    getRegion(I.getPointerOperand());
  }
  void visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst &I) {
    getRegion(I.getPointerOperand());
  }
  void visitAtomicRMWInst(llvm::AtomicRMWInst &I) {
    getRegion(I.getPointerOperand());
  }
  void visitCallInst(llvm::CallInst& I) {
    if (I.getType()->isPointerTy())
      getRegion(&I);
  }
};

}

#endif // REGIONS_H
