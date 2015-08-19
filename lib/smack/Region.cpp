//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/Region.h"
#include "smack/SmackOptions.h"

namespace smack {

DSAAliasAnalysis* Region::DSA = nullptr;

namespace {
  const Function* getFunction(const Value* V) {
    if (const Instruction *I = dyn_cast<Instruction>(V))
      return I->getParent()->getParent();
    else if (const Argument *A = dyn_cast<Argument>(V))
      return A->getParent();
    else if (const BasicBlock *BB = dyn_cast<BasicBlock>(V))
      return BB->getParent();

    // XXX I know this looks bad, but it works for now
    for (auto U : V->users())
      return getFunction(U);

    llvm_unreachable("Unexpected value.");
  }

  bool isFieldDisjoint(DSAAliasAnalysis* DSA, const Value* V, unsigned offset) {
    if (const GlobalValue* G = dyn_cast<GlobalValue>(V))
      return DSA->isFieldDisjoint(G, offset);
    else
      return DSA->isFieldDisjoint(V, getFunction(V));
  }
}

void Region::init(const Value* V, unsigned offset, unsigned length) {
  Type* T = V->getType();
  while (T->isPointerTy()) T = T->getPointerElementType();
  representative = DSA ? DSA->getNode(V) : nullptr;
  this->offset = offset;
  this->length = length;
  allocated = DSA && DSA->isAlloced(V);
  singleton = DSA && DSA->isSingletonGlobal(V) && T->isSingleValueType();
  bytewise = DSA && SmackOptions::BitPrecise &&
    (SmackOptions::NoByteAccessInference || !isFieldDisjoint(DSA,V,offset));
}

Region::Region(const Value* V) {
  unsigned offset = DSA ? DSA->getOffset(V) : 0;
  unsigned length = DSA ? DSA->getPointedTypeSize(V) :
    std::numeric_limits<unsigned>::max();
  init(V, offset, length);
}

Region::Region(const Value* V, unsigned length) {
  unsigned offset = DSA ? DSA->getOffset(V) : 0;
  init(V, offset, length);
}

Region::Region(const Value* V, unsigned offset, unsigned length) {
  init(V, offset, length);
}

bool Region::isIncomplete() {
  return !representative
      || representative->isIncompleteNode();
}

bool Region::isComplicated() {
  return !representative
      || representative->isIntToPtrNode()
      || representative->isIntToPtrNode()
      || representative->isExternalNode()
      || representative->isUnknownNode();
}

bool Region::isDisjoint(unsigned offset, unsigned length) {
  return this->offset + this->length <= offset
      || offset + length <= this->offset;
}


void Region::merge(Region& R) {
  assert(singleton == R.singleton);
  unsigned long low = std::min(offset, R.offset);
  unsigned long high = std::max(offset + length, R.offset + R.length);
  offset = low;
  length = high - low;
  bytewise = bytewise || R.bytewise;
  allocated = allocated || R.allocated;
}

bool Region::overlaps(Region& R) {
  return (isIncomplete() && R.isIncomplete())
      || (isComplicated() && R.isComplicated())
      || (representative == R.representative
          && (representative->isCollapsedNode()
              || !isDisjoint(R.offset, R.length)));
}

void Region::print(raw_ostream& O) {
  O << "<Node>[" << offset << "," << (offset + length) << "]{";
  if (singleton) O << "S";
  if (bytewise) O << "B";
  if (allocated) O << "A";
  O << "}";
}

void RegionCollector::visitLoadInst(LoadInst& I) {
  collect(I.getPointerOperand());
}

void RegionCollector::visitStoreInst(StoreInst& I) {
  collect(I.getPointerOperand());
}

void RegionCollector::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
  collect(I.getPointerOperand());
}

void RegionCollector::visitAtomicRMWInst(AtomicRMWInst &I) {
  collect(I.getPointerOperand());
}

void RegionCollector::visitMemIntrinsic(MemIntrinsic &I) {
  unsigned length = dyn_cast<ConstantInt>(I.getLength())->getZExtValue();
  collectWithLength(I.getDest(),length);
}

void RegionCollector::visitCallInst(CallInst& I) {
  if (I.getType()->isPointerTy())
    collect(&I);
}

} // namespace smack
