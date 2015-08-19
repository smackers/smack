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
  const DSNode* representative;
  unsigned offset;
  unsigned length;
  bool allocated;
  bool singleton;
  bool bytewise;
  bool memcpyd;
  bool staticInitd;

  static DSAAliasAnalysis* DSA;
  static DSAAliasAnalysis* getDSA() { return DSA; }

  void init(const Value* V, unsigned offset, unsigned length);

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
  Region(const Value* V);
  Region(const Value* V, unsigned offset, unsigned length);

  static void setDSA(DSAAliasAnalysis& dsa) { DSA = &dsa; }

  void merge(Region& R);
  bool overlaps(Region& R);

  bool isAllocated() const {
    return allocated;
  }

  bool isSingletonGlobal() const {
    return singleton;
  }

  bool bytewiseAccess() const {
    return bytewise;
  }

};

class RegionCollector : public InstVisitor<RegionCollector> {

  std::function<void(const Value*)> collect;

public:
  RegionCollector(std::function<void(const Value*)> fn) : collect(fn) { }

  // void visitModule(Module& M) {
  //   for (const GlobalValue& G : M.globals())
  //     collect(&G);
  // }

  // void visitAllocaInst(AllocaInst& I) {
    // getRegion(&I);
  // }

  void visitLoadInst(LoadInst& I) {
    collect(I.getPointerOperand());
  }

  void visitStoreInst(StoreInst& I) {
    collect(I.getPointerOperand());
  }

  void visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
    collect(I.getPointerOperand());
  }

  void visitAtomicRMWInst(AtomicRMWInst &I) {
    collect(I.getPointerOperand());
  }

  void visitMemIntrinsic(MemIntrinsic &I) {
    collect(I.getDest());
  }

  void visitCallInst(CallInst& I) {
    if (I.getType()->isPointerTy())
      collect(&I);
  }

};

}

#endif // REGION_H
