//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REGIONMANAGER_H
#define REGIONMANAGER_H

#include "smack/DSAAliasAnalysis.h"
#include "smack/Region.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InstVisitor.h"

namespace smack {

using namespace std;

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
  // TODO: Why invoking for alloca?
  void visitAllocaInst(llvm::AllocaInst& I) {
    // getRegion(&I);
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
  // TODO: Why invoking for call?
  void visitCallInst(llvm::CallInst& I) {
    // if (I.getType()->isPointerTy())
    //  getRegion(&I);
  }
};

}

#endif // REGIONMANAGER_H
