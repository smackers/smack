//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REGION_H
#define REGION_H

#include "dsa/DSGraph.h"
#include "smack/DSAAliasAnalysis.h"

namespace smack {

class Region {
private:
  const llvm::DSNode* representative;
  unsigned offset;
  unsigned length;
  bool allocated;
  bool singleton;
  bool memcpyd;
  bool staticInitd;

  bool isIncomplete() {
    return !representative
        || representative->isIncompleteNode();
  }

  bool isComplicated() {
    return !representative
        || representative->isIntToPtrNode()
        || representative->isIntToPtrNode()
        || representative->isExternalNode()
        || representative->isUnknownNode();
  }

  bool isDisjoint(unsigned offset, unsigned length) {
    return this->offset + this->length <= offset
        || offset + length <= this->offset;
  }

public:
  Region(const llvm::Value* V, unsigned offset, unsigned length, DSAAliasAnalysis* AA);
  void merge(Region& R);
  bool overlaps(Region& R);

  bool isAllocated() const {
    return allocated;
  }

  bool isSingletonGlobal() const {
    return singleton;
  }

};

class RegionCollector : public llvm::InstVisitor<RegionCollector> {

  std::function<void(const llvm::Value*)> collect;

public:
  RegionCollector(std::function<void(const llvm::Value*)> fn) : collect(fn) { }

  // void visitModule(llvm::Module& M) {
  //   for (const GlobalValue& G : M.globals())
  //     collect(&G);
  // }

  // void visitAllocaInst(llvm::AllocaInst& I) {
    // getRegion(&I);
  // }

  void visitLoadInst(llvm::LoadInst& I) {
    collect(I.getPointerOperand());
  }

  void visitStoreInst(llvm::StoreInst& I) {
    collect(I.getPointerOperand());
  }

  void visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst &I) {
    collect(I.getPointerOperand());
  }

  void visitAtomicRMWInst(llvm::AtomicRMWInst &I) {
    collect(I.getPointerOperand());
  }

  void visitMemIntrinsic(MemIntrinsic &I) {
    collect(I.getDest());
  }

  void visitCallInst(llvm::CallInst& I) {
    if (I.getType()->isPointerTy())
      collect(&I);
  }

};

}

#endif // REGION_H
