//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/Regions.h"
#include "smack/DSAWrapper.h"
#include "smack/DSAWrapperAnalysis.h"
#include "smack/Debug.h"
#include "smack/InitializePasses.h"
#include "smack/LlvmCompat.h"
#include "smack/SmackOptions.h"
#include "smack/SmackPipeline.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <utility>

#define DEBUG_TYPE "regions"

namespace smack {

const DataLayout *Region::DL = nullptr;
DSAWrapper *Region::DSA = nullptr;

namespace {

Function *queryFunctionForValue(const Value *V) {
  if (auto *I = dyn_cast<Instruction>(V))
    return const_cast<Function *>(I->getFunction());
  if (auto *A = dyn_cast<Argument>(V))
    return const_cast<Function *>(A->getParent());
  if (auto *BB = dyn_cast<BasicBlock>(V))
    return const_cast<Function *>(BB->getParent());
  return nullptr;
}

// Opaque-pointer-safe access-type recovery: SMACK runs under opaque pointers,
// where PointerType::getElementType() is gone. Recover the element type from a
// load/store user of the pointer; callers fall back to i8 when none is found.
const Type *accessTypeFromUsers(const Value *V) {
  for (const User *u : V->users()) {
    if (auto *L = dyn_cast<LoadInst>(u)) {
      if (L->getPointerOperand() == V)
        return L->getType();
    } else if (auto *S = dyn_cast<StoreInst>(u)) {
      if (S->getPointerOperand() == V)
        return S->getValueOperand()->getType();
    }
  }
  return nullptr;
}

} // namespace

void Region::init(Module &M, Pass &P) {
  DL = &M.getDataLayout();
  DSA = &P.getAnalysis<DSAWrapper>();
}

void Region::init(Module &M, DSAWrapper &dsa) {
  DL = &M.getDataLayout();
  DSA = &dsa;
}

bool Region::isSingleton(const Value *v, unsigned length) {
  // TODO can we do something for non-global nodes?
  auto node = DSA->getNode(v);

  return !isAllocated(node) && DSA->getNumGlobals(node) == 1 &&
         !DSA->isArray(node) && DSA->isTypeSafe(v) && !DSA->isMemOpd(node);
}

bool Region::isAllocated(MemNodeRef N) { return DSA->isAllocated(N); }

bool Region::isComplicated(MemNodeRef N) { return DSA->isComplicated(N); }

void Region::init(const Value *V, const Type *accessType, unsigned length) {
  assert(V->getType()->isPointerTy() && "Expected pointer argument.");
  const Type *memoryType = accessType ? accessType : accessTypeFromUsers(V);
  if (!memoryType)
    memoryType = Type::getInt8Ty(V->getContext());
  context = &V->getContext();
  pointer = V;
  function = queryFunctionForValue(V);
  representative =
      (DSA && !dyn_cast<ConstantPointerNull>(V)) ? DSA->getNode(V) : nullptr;
  this->type = memoryType;
  this->offset = DSA ? DSA->getOffset(V) : 0;
  this->length = length;

  singleton = DL && representative && isSingleton(V, length);
  allocated = !representative || isAllocated(representative);
  bytewise = DSA && SmackOptions::BitPrecise &&
             (SmackOptions::NoByteAccessInference ||
              (!representative || !DSA->isTypeSafe(V)) ||
              (memoryType && memoryType->isIntegerTy(8)));
  incomplete = !representative || DSA->isIncomplete(representative);
  complicated = !representative || isComplicated(representative);
  collapsed = !representative || DSA->isCollapsed(representative);
}

Region::Region(const Value *V) {
  unsigned length =
      DSA ? DSA->getPointedTypeSize(V) : std::numeric_limits<unsigned>::max();
  init(V, nullptr, length);
}

Region::Region(const Value *V, unsigned length) { init(V, nullptr, length); }

Region::Region(const Value *V, const Type *accessType) {
  unsigned length = std::numeric_limits<unsigned>::max();
  if (accessType && accessType->isSized() && DL)
    length = fixedTypeStoreSize(*DL, accessType);
  else if (DSA)
    length = DSA->getPointedTypeSize(V);
  init(V, accessType, length);
}

Region::Region(const Value *V, const Type *accessType, unsigned length) {
  init(V, accessType, length);
}

Region::Region(const LoadInst &I) {
  unsigned length = std::numeric_limits<unsigned>::max();
  if (I.getType()->isSized() && DL)
    length = fixedTypeStoreSize(*DL, I.getType());
  else if (DSA)
    length = DSA->getPointedTypeSize(I.getPointerOperand());
  init(I.getPointerOperand(), I.getType(), length);
}

Region::Region(const StoreInst &I) {
  const Type *accessType = I.getValueOperand()->getType();
  unsigned length = std::numeric_limits<unsigned>::max();
  if (accessType->isSized() && DL)
    length = fixedTypeStoreSize(*DL, accessType);
  else if (DSA)
    length = DSA->getPointedTypeSize(I.getPointerOperand());
  init(I.getPointerOperand(), accessType, length);
}

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
  type = (bytewise || collapse) ? nullptr : type;
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

} // namespace smack

char smack::Regions::ID = 0;

using namespace smack;
INITIALIZE_PASS(Regions, "smack-regions", "SMACK Memory Regions Pass", false,
                false)

namespace smack {

void Regions::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  if (!SmackOptions::NoMemoryRegionSplitting)
    AU.addRequired<DSAWrapper>();
}

void Regions::runImpl(Module &M, DSAWrapper &dsa) {
  regions.clear();
  if (!SmackOptions::NoMemoryRegionSplitting) {
    Region::init(M, dsa);
    visit(M);
  }
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
  regions.clear();
  if (!SmackOptions::NoMemoryRegionSplitting) {
    Region::init(M, *this);
    visit(M);
  }

  return false;
}

llvm::AnalysisKey RegionsAnalysis::Key;

RegionsAnalysis::Result
RegionsAnalysis::run(Module &M, llvm::ModuleAnalysisManager &MAM) {
  RegionsResult r;
  r.regions = std::make_unique<Regions>();
  if (!SmackOptions::NoMemoryRegionSplitting) {
    auto &dsa = MAM.getResult<DSAWrapperAnalysis>(M);
    r.regions->runImpl(M, *dsa.wrapper);
  }
  return r;
}

unsigned Regions::size() const { return regions.size(); }

Region &Regions::get(unsigned R) { return regions[R]; }

void Regions::snapshotReport(SmackMemoryPartitionReport &report) const {
  // Region-level diagnostics only. The oracle/SVF-evidence counters that the
  // old sea-dsa+oracle path filled stay at their zero defaults (the feature is
  // gone). This keeps llvm2bpl's --memory-partition-report JSON populated for
  // the SVF-andersen partition without resurrecting the oracle machinery.
  report.partitioner = "svf-andersen";
  report.dsaMode = "svf-andersen";
  report.regionCount = regions.size();

  unsigned noRepresentative = 0;
  for (const auto &region : regions) {
    if (region.isSingleton())
      ++report.singletonCount;
    if (region.isAllocated())
      ++report.allocatedCount;
    if (region.bytewiseAccess())
      ++report.bytewiseCount;
    if (region.isIncomplete())
      ++report.incompleteCount;
    if (region.isComplicated())
      ++report.complicatedCount;
    if (region.isCollapsed())
      ++report.collapsedCount;
    if (region.getType())
      ++report.typedCount;
    else
      ++report.untypedCount;
    if (!region.hasRepresentative())
      ++noRepresentative;
  }

  report.fallbackReasons.clear();
  if (noRepresentative)
    report.fallbackReasons.push_back({"no-representative", noRepresentative});
  if (report.incompleteCount)
    report.fallbackReasons.push_back({"incomplete", report.incompleteCount});
  if (report.complicatedCount)
    report.fallbackReasons.push_back({"complicated", report.complicatedCount});
  if (report.collapsedCount)
    report.fallbackReasons.push_back({"collapsed", report.collapsedCount});
  if (report.bytewiseCount)
    report.fallbackReasons.push_back({"bytewise", report.bytewiseCount});
  if (report.untypedCount)
    report.fallbackReasons.push_back({"untyped", report.untypedCount});
}

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

unsigned Regions::idx(const Value *V, const Type *accessType) {
  SDEBUG(errs() << "[regions] for: " << *V << " with access type ";
         if (accessType) accessType->print(errs()); else errs() << "<unknown>";
         errs() << "\n";);
  Region R(V, accessType);
  return idx(R);
}

unsigned Regions::idx(const Value *V, const Type *accessType,
                      unsigned length) {
  SDEBUG(errs() << "[regions] for: " << *V << " with access type ";
         if (accessType) accessType->print(errs()); else errs() << "<unknown>";
         errs() << " and length " << length << "\n";);
  Region R(V, accessType, length);
  return idx(R);
}

unsigned Regions::idx(const LoadInst &I) {
  SDEBUG(errs() << "[regions] for load access: " << I << "\n";);
  Region R(I);
  return idx(R);
}

unsigned Regions::idx(const StoreInst &I) {
  SDEBUG(errs() << "[regions] for store access: " << I << "\n";);
  Region R(I);
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

void Regions::visitLoadInst(LoadInst &I) { idx(I); }

void Regions::visitStoreInst(StoreInst &I) { idx(I); }

void Regions::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
  idx(I.getPointerOperand(), I.getCompareOperand()->getType());
}

void Regions::visitAtomicRMWInst(AtomicRMWInst &I) {
  idx(I.getPointerOperand(), I.getValOperand()->getType());
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
    assert(I.arg_size() == 2 && "Expected two operands.");
    const Value *P = I.getArgOperand(0);
    const Value *N = I.getArgOperand(1);

    while (isa<const CastInst>(P))
      P = dyn_cast<const CastInst>(P)->getOperand(0);
    assert(P->getType()->isPointerTy() && "Expected pointer argument.");

    if (auto CI = dyn_cast<ConstantInt>(N)) {
      const unsigned bound = CI->getZExtValue();
      const DataLayout &DL = I.getModule()->getDataLayout();
      // Opaque-pointer-safe element type: recover from a load/store access of P
      // (PointerType::getElementType() is removed under opaque pointers). Fall
      // back to i8 as Region::init does.
      const Type *T = accessTypeFromUsers(P);
      if (!T)
        T = Type::getInt8Ty(I.getContext());
      const unsigned size = fixedTypeStoreSize(DL, T);
      const unsigned length = bound * size;
      idx(P, T, length);

    } else {
      llvm_unreachable("Non-constant size expression not yet handled.");
    }
  }
}

} // namespace smack
