//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/Regions.h"
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"

#define DEBUG_TYPE "regions"

namespace smack {

const DataLayout *Region::DL = nullptr;
DSAWrapper *Region::DSA = nullptr;

void Region::init(Module &M, Pass &P) {
  DL = &M.getDataLayout();
  DSA = &P.getAnalysis<DSAWrapper>();
}

bool Region::isSingleton(const Value *v, unsigned length) {
  // TODO can we do something for non-global nodes?
  auto node = DSA->getNode(v);

  return !isAllocated(node) && DSA->getNumGlobals(node) == 1 &&
         !node->isArray() && DSA->isTypeSafe(v) && !DSA->isMemOpd(node);
}

bool Region::isAllocated(const seadsa::Node *N) {
  return N->isHeap() || N->isAlloca();
}

bool Region::isComplicated(const seadsa::Node *N) {
  return N->isIntToPtr() || N->isPtrToInt() || N->isExternal() ||
         N->isUnknown();
}

void Region::init(const Value *V, unsigned length) {
  Type *T = V->getType();
  assert(T->isPointerTy() && "Expected pointer argument.");
  T = T->getPointerElementType();
  context = &V->getContext();
  representative =
      (DSA && !dyn_cast<ConstantPointerNull>(V)) ? DSA->getNode(V) : nullptr;
  this->type = T;
  this->offset = DSA ? DSA->getOffset(V) : 0;
  this->length = length;

  singleton = DL && representative && isSingleton(V, length);
  allocated = !representative || isAllocated(representative);
  bytewise = DSA && SmackOptions::BitPrecise &&
             (SmackOptions::NoByteAccessInference ||
              (!representative || !DSA->isTypeSafe(V)) || T->isIntegerTy(8));
  incomplete = !representative || representative->isIncomplete();
  complicated = !representative || isComplicated(representative);
  collapsed = !representative || representative->isOffsetCollapsed();
}

Region::Region(const Value *V) {
  unsigned length =
      DSA ? DSA->getPointedTypeSize(V) : std::numeric_limits<unsigned>::max();
  init(V, length);
}

Region::Region(const Value *V, unsigned length) { init(V, length); }

bool Region::isDisjoint(unsigned offset, unsigned length) {
  return this->offset + this->length <= offset ||
         offset + length <= this->offset;
}

void Region::merge(Region &R) {
  bool collapse = type != R.type;
  unsigned long low = std::min(offset, R.offset);
  unsigned long high = std::max(offset + length, R.offset + R.length);
  offset = low;
  length = high - low;
  singleton = singleton && R.singleton;
  allocated = allocated || R.allocated;
  bytewise = SmackOptions::BitPrecise && (bytewise || R.bytewise || collapse);
  incomplete = incomplete || R.incomplete;
  complicated = complicated || R.complicated;
  collapsed = collapsed || R.collapsed;
  type = (bytewise || collapse) ? NULL : type;
}

bool Region::overlaps(Region &R) {
  return (incomplete && R.incomplete) || (complicated && R.complicated) ||
         (representative == R.representative &&
          (collapsed || !isDisjoint(R.offset, R.length)));
}

void Region::print(raw_ostream &O) {
  // TODO identify the representative
  O << "<Node:";
  if (type)
    O << *type;
  else
    O << "*";
  O << ">[" << offset << "," << (offset + length) << "]{";
  if (singleton)
    O << "S";
  if (bytewise)
    O << "B";
  if (complicated)
    O << "C";
  if (incomplete)
    O << "I";
  if (collapsed)
    O << "L";
  if (allocated)
    O << "A";
  O << "}";
}

char Regions::ID;
RegisterPass<Regions> RegionsPass("smack-regions", "SMACK Memory Regions Pass");

void Regions::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  if (!SmackOptions::NoMemoryRegionSplitting)
    AU.addRequired<DSAWrapper>();
}

bool Regions::runOnModule(Module &M) {
  // Shaobo: my understanding of how this class works:
  // First, a bunch of instructions involving pointers are visited (via
  // Regions::idx). During a visit on an instruction, a region is created
  // (Region::init) for the pointer operand. Note that a region is always
  // created for a pointer when it's visited, regardless of whether it alias
  // with the existing ones.  A region can be roughly seen as a tuple of (cell,
  // length) or (node, offset, length) since a cell is essentially a tuple of
  // (node, offset). After a region is created, we will merge it to the existing
  // ones if it overlaps with the them. So after this pass, we will get a bunch
  // of regions which are mutually exclusive to each other.
  // After that, SmackRep will call Regions::idx to get the region for a pointer
  // operand, which repeats the aforementioned process. Note that we don't have
  // fancy caching, so a region is created and merged everytime Regions::idx
  // is called.
  if (!SmackOptions::NoMemoryRegionSplitting) {
    Region::init(M, *this);
    visit(M);
  }

  return false;
}

unsigned Regions::size() const { return regions.size(); }

Region &Regions::get(unsigned R) { return regions[R]; }

unsigned Regions::idx(const Value *V) {
  SDEBUG(errs() << "[regions] for: " << *V << "\n"; auto U = V;
         while (U && !isa<Instruction>(U) && !U->use_empty()) U =
             U->user_back();
         if (auto I = dyn_cast<Instruction>(U)) {
           auto F = I->getParent()->getParent();
           if (I != V)
             errs() << "  at instruction: " << *I << "\n";
           errs() << "  in function: " << F->getName() << "\n";
         });
  Region R(V);
  return idx(R);
}

unsigned Regions::idx(const Value *V, unsigned length) {
  SDEBUG(errs() << "[regions] for: " << *V << " with length " << length << "\n";
         auto U = V; while (U && !isa<Instruction>(U) && !U->use_empty()) U =
                         U->user_back();
         if (auto I = dyn_cast<Instruction>(U)) {
           auto F = I->getParent()->getParent();
           if (I != V)
             errs() << "  at instruction: " << *I << "\n";
           errs() << "  in function: " << F->getName() << "\n";
         });
  Region R(V, length);
  return idx(R);
}

unsigned Regions::idx(Region &R) {
  unsigned r;

  SDEBUG(errs() << "[regions]   using region: ");
  SDEBUG(R.print(errs()));
  SDEBUG(errs() << "\n");

  for (r = 0; r < regions.size(); ++r) {
    if (regions[r].overlaps(R)) {

      SDEBUG(errs() << "[regions]   found overlap at index " << r << ": ");
      SDEBUG(regions[r].print(errs()));
      SDEBUG(errs() << "\n");

      regions[r].merge(R);

      SDEBUG(errs() << "[regions]   merged region: ");
      SDEBUG(regions[r].print(errs()));
      SDEBUG(errs() << "\n");

      break;
    }
  }

  if (r == regions.size())
    regions.emplace_back(R);

  else {
    // Here is the tricky part: in case R was merged with an existing region,
    // we must now also merge any other region which intersects with R.
    unsigned q = r + 1;
    while (q < regions.size()) {
      if (regions[r].overlaps(regions[q])) {

        SDEBUG(errs() << "[regions]   found extra overlap at index " << q
                      << ": ");
        SDEBUG(regions[q].print(errs()));
        SDEBUG(errs() << "\n");

        regions[r].merge(regions[q]);
        regions.erase(regions.begin() + q);

        SDEBUG(errs() << "[regions]   merged region: ");
        SDEBUG(regions[r].print(errs()));
        SDEBUG(errs() << "\n");

      } else {
        q++;
      }
    }
  }

  SDEBUG(errs() << "[regions]   returning index: " << r << "\n\n");

  return r;
}

void Regions::visitLoadInst(LoadInst &I) { idx(I.getPointerOperand()); }

void Regions::visitStoreInst(StoreInst &I) { idx(I.getPointerOperand()); }

void Regions::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
  idx(I.getPointerOperand());
}

void Regions::visitAtomicRMWInst(AtomicRMWInst &I) {
  idx(I.getPointerOperand());
}

void Regions::visitMemSetInst(MemSetInst &I) {
  unsigned length;

  if (auto CI = dyn_cast<ConstantInt>(I.getLength()))
    length = CI->getZExtValue();
  else
    length = std::numeric_limits<unsigned>::max();

  idx(I.getDest(), length);
}

void Regions::visitMemTransferInst(MemTransferInst &I) {
  unsigned length;

  if (auto CI = dyn_cast<ConstantInt>(I.getLength()))
    length = CI->getZExtValue();
  else
    length = std::numeric_limits<unsigned>::max();

  // We need to visit the source location otherwise
  // extra merges will happen in the translation phrase,
  // resulting in ``hanging'' regions.
  idx(I.getSource(), length);
  idx(I.getDest(), length);
}

void Regions::visitCallInst(CallInst &I) {
  Function *F = I.getCalledFunction();
  std::string name = F && F->hasName() ? F->getName().str() : "";

  if (F && F->isDeclaration() && I.getType()->isPointerTy() && name != "malloc")
    idx(&I);

  if (name.find("__SMACK_values") != std::string::npos) {
    assert(I.getNumArgOperands() == 2 && "Expected two operands.");
    const Value *P = I.getArgOperand(0);
    const Value *N = I.getArgOperand(1);

    while (isa<const CastInst>(P))
      P = dyn_cast<const CastInst>(P)->getOperand(0);
    const PointerType *T = dyn_cast<PointerType>(P->getType());
    assert(T && "Expected pointer argument.");

    if (auto I = dyn_cast<ConstantInt>(N)) {
      const unsigned bound = I->getZExtValue();
      const unsigned size = T->getElementType()->getIntegerBitWidth() / 8;
      const unsigned length = bound * size;
      idx(P, length);

    } else {
      llvm_unreachable("Non-constant size expression not yet handled.");
    }
  }
}

} // namespace smack
