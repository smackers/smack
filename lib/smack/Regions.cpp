//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/Regions.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"

#define DEBUG_TYPE "smack-region"

namespace smack {

const DataLayout* Region::DL = nullptr;
DSAAliasAnalysis* Region::DSA = nullptr;
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

  bool isFieldDisjoint(DSAAliasAnalysis* DSA, const Value* V, unsigned offset) {
    if (const GlobalValue* G = dyn_cast<GlobalValue>(V))
      return DSA->isFieldDisjoint(G, offset);
    else
      return DSA->isFieldDisjoint(V, getFunction(V));
  }

  unsigned getRealOffset(const DataLayout* DL, const Value* V) {
    auto CE = dyn_cast<ConstantExpr>(V);
    if (!CE || CE->getOpcode() != Instruction::GetElementPtr)
      return 0;

    unsigned offset = 0;
    gep_type_iterator TI = gep_type_begin(CE);

    for (unsigned i=1; i < CE->getNumOperands(); ++i, ++TI) {
      const Value* A = CE->getOperand(i);
      Type* T = *TI;
      if (auto ST = dyn_cast<StructType>(T)) {
        auto CI = dyn_cast<ConstantInt>(A);
        assert(CI && "Expected constant struct index.");
        offset += DL->getStructLayout(ST)->getElementOffset(CI->getZExtValue());
      }

      else if (auto ST = dyn_cast<SequentialType>(T)) {
        if (auto CI = dyn_cast<ConstantInt>(A))
          offset += DL->getTypeStoreSize(ST->getElementType())
            * CI->getZExtValue();
        else
          return std::numeric_limits<unsigned>::max();

      } else
        llvm_unreachable("Unexpected offset type.");
    }

    return offset;
  }
}

void Region::init(Module& M, Pass& P) {
  DL = M.getDataLayout();
  DSA = &P.getAnalysis<DSAAliasAnalysis>();
}

bool Region::isSingleton(const DSNode* N, unsigned offset, unsigned length) {
  if (N->isGlobalNode()
      && N->numGlobals() == 1
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
      while (T->isPointerTy()) T = T->getPointerElementType();
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
  while (T->isPointerTy()) T = T->getPointerElementType();
  context = &V->getContext();
  representative = DSA ? DSA->getNode(V) : nullptr;
  this->type = T;
  this->offset = DSA ? DSA->getOffset(V) : 0;
  this->length = length;

  singleton = DL && representative

    // NOTE this prevents us from considering array accesses as singletons
    && this->offset == getRealOffset(DL,V)

    && isSingleton(representative, offset, length);

  allocated = !representative || isAllocated(representative);
  bytewise = DSA && SmackOptions::BitPrecise &&
    (SmackOptions::NoByteAccessInference || !isFieldDisjoint(DSA,V,offset) ||
    T->isIntegerTy(8));
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
    AU.addRequired<DataLayoutPass>();
    AU.addRequiredTransitive<LocalDataStructures>();
    AU.addRequiredTransitive<BUDataStructures>();
    AU.addRequiredTransitive<TDDataStructures>();
    AU.addRequiredTransitive<DSNodeEquivs>();
    AU.addRequiredTransitive<dsa::TypeSafety<TDDataStructures> >();
    AU.addRequired<DSAAliasAnalysis>();
  }
}

bool Regions::runOnModule(Module& M) {
  if (!SmackOptions::NoMemoryRegionSplitting) {
    Region::init(M,*this);

    DataStructures
      &local = getAnalysis<LocalDataStructures>(),
      &BU = getAnalysis<BUDataStructures>(),
      &TD = getAnalysis<TDDataStructures>();
    DSNodeEquivs
      &EQ = getAnalysis<DSNodeEquivs>();

    DEBUG(
      local.print(errs(), &M);
      BU.print(errs(), &M);
      TD.print(errs(), &M);
    );

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
  DEBUG(errs() << "[regions] getting index for: " << *V << "\n");
  Region R(V);
  return idx(R);
}

unsigned Regions::idx(const Value* V, unsigned length) {
  DEBUG(errs() << "[regions] getting index for: " << *V
               << " with length " << length << "\n");
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

  DEBUG(errs() << "[regions]   returning index: " << r << "\n");

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
  string name = F && F->hasName() ? F->getName().str() : "";

  if (I.getType()->isPointerTy())
    idx(&I);

  if (name.find("__SMACK_object") != string::npos) {
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
