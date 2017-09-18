//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "dsa/DSNode.h"
#include "dsa/DSGraph.h"
#include "dsa/DataStructure.h"
#include "dsa/TypeSafety.h"
#include "assistDS/DSNodeEquivs.h"
#include "smack/Regions.h"
#include "smack/SmackOptions.h"
#include "smack/DSAWrapper.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "smack/Debug.h"

#define DEBUG_TYPE "regions"

namespace smack {

const DataLayout* Region::DL = nullptr;
DSAWrapper* Region::DSA = nullptr;
// DSNodeEquivs* Region::NEQS = nullptr;

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

  bool isFieldDisjoint(DSAWrapper* DSA, const Value* V, unsigned offset) {
    if (const GlobalValue* G = dyn_cast<GlobalValue>(V))
      return DSA->isFieldDisjoint(G, offset);
    else
      return DSA->isFieldDisjoint(V, getFunction(V));
  }

}

void Region::init(Module& M, Pass& P) {
  DL = &M.getDataLayout();
  DSA = &P.getAnalysis<DSAWrapper>();
}

namespace {
  unsigned numGlobals(const DSNode* N) {
    unsigned count = 0;

    // shamelessly ripped from getCaption(..) in lib/DSA/Printer.cpp
    EquivalenceClasses<const GlobalValue*> *GlobalECs = 0;
    const DSGraph *G = N->getParentGraph();
    if (G) GlobalECs = &G->getGlobalECs();

    for (auto i = N->globals_begin(), e = N->globals_end(); i != e; ++i) {
      count += 1;

      if (GlobalECs) {
        // Figure out how many globals are equivalent to this one.
        auto I = GlobalECs->findValue(*i);
        if (I != GlobalECs->end()) {
          count += std::distance(
            GlobalECs->member_begin(I), GlobalECs->member_end()) - 1;
        }
      }
    }

    return count;
  }
}

bool Region::isSingleton(const DSNode* N, unsigned offset, unsigned length) {
  if (N->isGlobalNode()
      && numGlobals(N) == 1
      && !N->isArrayNode()
      && !N->isAllocaNode()
      && !N->isHeapNode()
      && !N->isExternalNode()
      && !N->isUnknownNode()) {

    // TODO can we do something for non-global nodes?

    // TODO don’t need to know if there are other members of this class, right?
    // assert(NEQS && "Missing DS node equivalence information.");
    // auto &Cs = NEQS->getEquivalenceClasses();
    // auto C = Cs.findValue(representative);
    // assert(C != Cs.end() && "No equivalence class found.");
    // assert(Cs.member_begin(C) != Cs.member_end() && "Found empty class.");
    // if (++(Cs.member_begin(C)) != Cs.member_end()) return false;

    assert(DL && "Missing data layout information.");

    for (auto I = N->type_begin(), E = N->type_end(); I != E; ++I) {
      if (I->first < offset) continue;
      if (I->first > offset) break;
      if (I->second->begin() == I->second->end()) break;
      if ((++(I->second->begin())) != I->second->end()) break;
      Type* T = *I->second->begin();
      if (!T->isSized()) break;
      if (DL->getTypeAllocSize(T) != length) break;
      if (!T->isSingleValueType()) break;
      return true;
    }
  }
  return false;
}

bool Region::isAllocated(const DSNode* N) {
  return N->isHeapNode()
      || N->isAllocaNode();
}

bool Region::isComplicated(const DSNode* N) {
  return N->isIntToPtrNode()
      || N->isIntToPtrNode()
      || N->isExternalNode()
      || N->isUnknownNode();
}

void Region::init(const Value* V, unsigned length) {
  Type* T = V->getType();
  assert (T->isPointerTy() && "Expected pointer argument.");
  T = T->getPointerElementType();
  context = &V->getContext();
  representative = (DSA && !dyn_cast<ConstantPointerNull>(V))
    ? DSA->getNode(V) : nullptr;
  this->type = T;
  int offset = DSA ? DSA->getOffset(V) : 0;
  if (offset < 0) {
    this->offset = 0;
    this->length = -1U;
  } else {
    this->offset = offset;
    this->length = length;
  }

  singleton = DL && representative
    && isSingleton(representative, offset, length);

  allocated = !representative || isAllocated(representative);
  bytewise = DSA && SmackOptions::BitPrecise &&
    (SmackOptions::NoByteAccessInference || !isFieldDisjoint(DSA,V,offset) ||
    DSA->isMemcpyd(representative) || T->isIntegerTy(8));
  incomplete = !representative || representative->isIncompleteNode();
  complicated = !representative || isComplicated(representative);
  collapsed = !representative || representative->isCollapsedNode();
}

Region::Region(const Value* V) {
  unsigned length = DSA ? DSA->getPointedTypeSize(V) :
    std::numeric_limits<unsigned>::max();
  init(V, length);
}

Region::Region(const Value* V, unsigned length) {
  init(V, length);
}

bool Region::isDisjoint(unsigned offset, unsigned length) {
  return this->offset + this->length <= offset
      || offset + length <= this->offset;
}

void Region::merge(Region& R) {
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

bool Region::overlaps(Region& R) {
  return (incomplete && R.incomplete)
      || (complicated && R.complicated)
      || (representative == R.representative
          && (collapsed || !isDisjoint(R.offset, R.length)));
}

void Region::print(raw_ostream& O) {
  // TODO identify the representative
  O << "<Node>[" << offset << "," << (offset + length) << "]{";
  if (isSingleton()) O << "S";
  if (bytewise) O << "B";
  if (isAllocated()) O << "A";
  O << "}";
}

char Regions::ID;
RegisterPass<Regions> RegionsPass("smack-regions", "SMACK Memory Regions Pass");

void Regions::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  if (!SmackOptions::NoMemoryRegionSplitting) {
    AU.addRequiredTransitive<llvm::LocalDataStructures>();
    AU.addRequiredTransitive<llvm::BUDataStructures>();
    AU.addRequiredTransitive<llvm::TDDataStructures>();
    AU.addRequiredTransitive<llvm::DSNodeEquivs>();
    AU.addRequiredTransitive<dsa::TypeSafety<llvm::TDDataStructures> >();
    AU.addRequired<DSAWrapper>();
  }
}

bool Regions::runOnModule(Module& M) {
  if (!SmackOptions::NoMemoryRegionSplitting) {
    Region::init(M,*this);
    visit(M);
  }

  return false;
}

unsigned Regions::size() const {
  return regions.size();
}

Region& Regions::get(unsigned R) {
  return regions[R];
}

unsigned Regions::idx(const Value* V) {
  DEBUG(
    errs() << "[regions] for: " << *V << "\n";
    auto U = V;
    while (U && !isa<Instruction>(U) && !U->use_empty()) U = U->user_back();
    if (auto I = dyn_cast<Instruction>(U)) {
      auto F = I->getParent()->getParent();
      if (I != V)
        errs() << "  at instruction: " << *I << "\n";
      errs() << "  in function: " << F->getName() << "\n";
    }
  );
  Region R(V);
  return idx(R);
}

unsigned Regions::idx(const Value* V, unsigned length) {
  DEBUG(
    errs() << "[regions] for: " << *V << " with length " << length << "\n";
    auto U = V;
    while (U && !isa<Instruction>(U) && !U->use_empty()) U = U->user_back();
    if (auto I = dyn_cast<Instruction>(U)) {
      auto F = I->getParent()->getParent();
      if (I != V)
        errs() << "  at instruction: " << *I << "\n";
      errs() << "  in function: " << F->getName() << "\n";
    }
  );
  Region R(V,length);
  return idx(R);
}

unsigned Regions::idx(Region& R) {
  unsigned r;

  DEBUG(errs() << "[regions]   using region: ");
  DEBUG(R.print(errs()));
  DEBUG(errs() << "\n");

  for (r = 0; r < regions.size(); ++r) {
    if (regions[r].overlaps(R)) {

      DEBUG(errs() << "[regions]   found overlap at index " << r << ": ");
      DEBUG(regions[r].print(errs()));
      DEBUG(errs() << "\n");

      regions[r].merge(R);

      DEBUG(errs() << "[regions]   merged region: ");
      DEBUG(regions[r].print(errs()));
      DEBUG(errs() << "\n");

      break;
    }
  }

  if (r == regions.size())
    regions.emplace_back(R);

  else {
    // Here is the tricky part: in case R was merged with an existing region,
    // we must now also merge any other region which intersects with R.
    unsigned q = r+1;
    while (q < regions.size()) {
      if (regions[r].overlaps(regions[q])) {

        DEBUG(errs() << "[regions]   found extra overlap at index " << q << ": ");
        DEBUG(regions[q].print(errs()));
        DEBUG(errs() << "\n");

        regions[r].merge(regions[q]);
        regions.erase(regions.begin()+q);

        DEBUG(errs() << "[regions]   merged region: ");
        DEBUG(regions[r].print(errs()));
        DEBUG(errs() << "\n");

      } else {
        q++;
      }
    }
  }

  DEBUG(errs() << "[regions]   returning index: " << r << "\n\n");

  return r;
}

void Regions::visitLoadInst(LoadInst& I) {
  idx(I.getPointerOperand());
}

void Regions::visitStoreInst(StoreInst& I) {
  idx(I.getPointerOperand());
}

void Regions::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
  idx(I.getPointerOperand());
}

void Regions::visitAtomicRMWInst(AtomicRMWInst &I) {
  idx(I.getPointerOperand());
}

void Regions::visitMemIntrinsic(MemIntrinsic &I) {
  unsigned length;

  if (auto CI = dyn_cast<ConstantInt>(I.getLength()))
    length = CI->getZExtValue();
  else
    length = std::numeric_limits<unsigned>::max();

  idx(I.getDest(),length);
}

void Regions::visitCallInst(CallInst& I) {
  Function* F = I.getCalledFunction();
  std::string name = F && F->hasName() ? F->getName().str() : "";

  if (I.getType()->isPointerTy())
    idx(&I);

  if (name.find("__SMACK_values") != std::string::npos) {
    assert(I.getNumArgOperands() == 2 && "Expected two operands.");
    const Value* P = I.getArgOperand(0);
    const Value* N = I.getArgOperand(1);

    while (isa<const CastInst>(P))
      P = dyn_cast<const CastInst>(P)->getOperand(0);
    const PointerType* T = dyn_cast<PointerType>(P->getType());
    assert(T && "Expected pointer argument.");

    if (auto I = dyn_cast<ConstantInt>(N)) {
      const unsigned bound = I->getZExtValue();
      const unsigned size = T->getElementType()->getIntegerBitWidth() / 8;
      const unsigned length = bound * size;
      idx(P,length);

    } else {
      llvm_unreachable("Non-constant size expression not yet handled.");
    }
  }
}

} // namespace smack
