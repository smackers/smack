//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/Regions.h"
#include "smack/DSAWrapperAnalysis.h"
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "smack/InitializePasses.h"
#include "smack/LlvmCompat.h"
#include "smack/MemoryPartitionOracle.h"
#include "smack/SmackPipeline.h"
#include "smack/SmackOptions.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <utility>

#define DEBUG_TYPE "regions"

namespace smack {

const DataLayout *Region::DL = nullptr;
DSAWrapper *Region::DSA = nullptr;
const SVFMemoryPartition *Region::SVFPartition = nullptr;
const MemoryPartitionOracle *Region::Oracle = nullptr;
unsigned *Region::OracleNoAliasCount = nullptr;
unsigned *Region::OracleMayAliasCount = nullptr;
unsigned *Region::OracleFallbackCount = nullptr;

namespace {

bool isSVFRefinedPartitioner() {
  return SmackOptions::MemoryPartitioner.getValue() == "svf-refined";
}

bool isSVFNativePartitioner() {
  return SmackOptions::MemoryPartitioner.getValue() == "svf-native";
}

bool usesExternalOraclePartitioner() {
  return isSVFRefinedPartitioner();
}

bool usesAARefinementPartitioner() {
  return SmackOptions::MemoryPartitioner.getValue() == "aa-refined";
}

bool usesOverlapRefinementPartitioner() {
  return usesAARefinementPartitioner() || isSVFRefinedPartitioner();
}

Function *queryFunctionForValue(const Value *V) {
  if (auto *I = dyn_cast<Instruction>(V))
    return const_cast<Function *>(I->getFunction());
  if (auto *A = dyn_cast<Argument>(V))
    return const_cast<Function *>(A->getParent());
  if (auto *BB = dyn_cast<BasicBlock>(V))
    return const_cast<Function *>(BB->getParent());
  return nullptr;
}

} // namespace

void Region::init(Module &M, Pass &P) {
  DL = &M.getDataLayout();
  DSA = &P.getAnalysis<DSAWrapper>();
  SVFPartition = nullptr;
  Oracle = nullptr;
  OracleNoAliasCount = nullptr;
  OracleMayAliasCount = nullptr;
  OracleFallbackCount = nullptr;
}

void Region::init(Module &M, DSAWrapper &dsa) {
  DL = &M.getDataLayout();
  DSA = &dsa;
  SVFPartition = nullptr;
  Oracle = nullptr;
  OracleNoAliasCount = nullptr;
  OracleMayAliasCount = nullptr;
  OracleFallbackCount = nullptr;
}

void Region::init(Module &M, DSAWrapper &dsa,
                  const MemoryPartitionOracle *oracle,
                  unsigned *oracleNoAliasCount,
                  unsigned *oracleMayAliasCount,
                  unsigned *oracleFallbackCount) {
  DL = &M.getDataLayout();
  DSA = &dsa;
  SVFPartition = nullptr;
  Oracle = oracle;
  OracleNoAliasCount = oracleNoAliasCount;
  OracleMayAliasCount = oracleMayAliasCount;
  OracleFallbackCount = oracleFallbackCount;
}

void Region::init(Module &M, const MemoryPartitionOracle *oracle,
                  unsigned *oracleNoAliasCount,
                  unsigned *oracleMayAliasCount,
                  unsigned *oracleFallbackCount) {
  DL = &M.getDataLayout();
  DSA = nullptr;
  SVFPartition = nullptr;
  Oracle = oracle;
  OracleNoAliasCount = oracleNoAliasCount;
  OracleMayAliasCount = oracleMayAliasCount;
  OracleFallbackCount = oracleFallbackCount;
}

void Region::init(Module &M, const SVFMemoryPartition *svfPartition,
                  unsigned *oracleNoAliasCount,
                  unsigned *oracleMayAliasCount,
                  unsigned *oracleFallbackCount) {
  DL = &M.getDataLayout();
  DSA = nullptr;
  SVFPartition = svfPartition;
  Oracle = svfPartition ? svfPartition->getOracle() : nullptr;
  OracleNoAliasCount = oracleNoAliasCount;
  OracleMayAliasCount = oracleMayAliasCount;
  OracleFallbackCount = oracleFallbackCount;
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

void Region::init(const Value *V, const Type *accessType, unsigned length,
                  bool addNativePointerEvidenceForValue) {
  Type *T = V->getType();
  assert(T->isPointerTy() && "Expected pointer argument.");
  const bool svfNative = isSVFNativePartitioner();
  const Type *memoryType =
      accessType ? accessType
                 : (DSA ? DSA->getPointedType(V) : legacyPointerElementType(V));
  context = &V->getContext();
  pointer = V;
  function = queryFunctionForValue(V);
  representative =
      (DSA && !dyn_cast<ConstantPointerNull>(V))
          ? DSA->getNode(V)
          : nullptr;
  this->type = memoryType;
  this->offset = DSA ? DSA->getOffset(V) : 0;
  this->length = length;
  accessEvidence.clear();
  evidenceRegionIds.clear();
  oracleIncomplete = svfNative;

  if (svfNative) {
    singleton = false;
    allocated = !isa<CallBase>(V);
    bytewise = SmackOptions::BitPrecise &&
               (SmackOptions::NoByteAccessInference || !memoryType ||
                memoryType->isIntegerTy(8));
    incomplete = false;
    complicated = false;
    collapsed = false;
    if (addNativePointerEvidenceForValue)
      addNativePointerEvidence(*V);
    return;
  }

  singleton = DL && representative && isSingleton(V, length);
  allocated = !representative || isAllocated(representative);
  bytewise = DSA && SmackOptions::BitPrecise &&
             (SmackOptions::NoByteAccessInference ||
              (!representative || !DSA->isTypeSafe(V)) ||
              (memoryType && memoryType->isIntegerTy(8)));
  incomplete = !representative || representative->isIncomplete();
  complicated = !representative || isComplicated(representative);
  collapsed = !representative || representative->isOffsetCollapsed();
}

void Region::addNativeEvidence(llvm::StringRef key,
                               const SVFMemoryPartition::Evidence &evidence) {
  if (!evidence.complete || evidence.regionIds.empty()) {
    std::string error = "svf-native missing memory evidence";
    if (!evidence.reason.empty())
      error += ": " + evidence.reason;
    report_fatal_error(StringRef(error), false);
  }

  MemoryAccessEvidence access;
  access.key = key.str();
  access.regionIds.assign(evidence.regionIds.begin(), evidence.regionIds.end());
  evidenceRegionIds.insert(evidence.regionIds.begin(), evidence.regionIds.end());
  accessEvidence.push_back(std::move(access));
  oracleIncomplete = false;
  incomplete = false;
  complicated = false;
  collapsed = false;
}

void Region::addNativePointerEvidence(const llvm::Value &V) {
  if (!SVFPartition) {
    report_fatal_error(
        "svf-native selected but no in-process SVF partition is available",
        false);
  }
  std::string key;
  raw_string_ostream os(key);
  os << "ptr:";
  V.print(os);
  addNativeEvidence(os.str(), SVFPartition->lookupPointer(V));
}

void Region::addAccessEvidence(const Instruction &I) {
  if (isSVFNativePartitioner()) {
    if (!SVFPartition) {
      report_fatal_error(
          "svf-native selected but no in-process SVF partition is available",
          false);
    }
    if (const auto *load = dyn_cast<LoadInst>(&I)) {
      addNativeEvidence(MemoryPartitionOracle::accessKey(I),
                        SVFPartition->lookupLoad(*load));
      return;
    }
    if (const auto *store = dyn_cast<StoreInst>(&I)) {
      addNativeEvidence(MemoryPartitionOracle::accessKey(I),
                        SVFPartition->lookupStore(*store));
      return;
    }
    report_fatal_error("svf-native does not support this memory instruction",
                       false);
  }

  if (!Oracle || !MemoryPartitionOracle::isSupportedAccess(I))
    return;

  const std::string key = MemoryPartitionOracle::accessKey(I);
  const auto *regionIds = Oracle->lookup(key);
  if (!regionIds || regionIds->empty())
    return;

  MemoryAccessEvidence evidence;
  evidence.key = key;
  evidence.regionIds.assign(regionIds->begin(), regionIds->end());
  evidenceRegionIds.insert(regionIds->begin(), regionIds->end());
  accessEvidence.push_back(std::move(evidence));
  oracleIncomplete = false;
  if (isSVFNativePartitioner()) {
    incomplete = false;
    complicated = false;
  }
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
  init(I.getPointerOperand(), I.getType(), length,
       /*addNativePointerEvidenceForValue=*/false);
  addAccessEvidence(I);
}

Region::Region(const StoreInst &I) {
  const Type *accessType = I.getValueOperand()->getType();
  unsigned length = std::numeric_limits<unsigned>::max();
  if (accessType->isSized() && DL)
    length = fixedTypeStoreSize(*DL, accessType);
  else if (DSA)
    length = DSA->getPointedTypeSize(I.getPointerOperand());
  init(I.getPointerOperand(), accessType, length,
       /*addNativePointerEvidenceForValue=*/false);
  addAccessEvidence(I);
}

bool Region::isDisjoint(unsigned offset, unsigned length) {
  return this->offset + this->length <= offset ||
         offset + length <= this->offset;
}

bool Region::aaProvesNoAlias(
    Region &R, llvm::function_ref<llvm::AAResults &(Function &)> getAA) {
  if (!pointer || !R.pointer || pointer == R.pointer)
    return false;

  Function *queryFunction = function ? function : R.function;
  if (!queryFunction || (function && R.function && function != R.function))
    return false;

  auto getLocation = [](const Region &Region) {
    // Region length uses UINT_MAX as "unknown"; do not turn that sentinel into
    // a huge precise query. Keeping it unknown is conservative for AA.
    if (Region.length == std::numeric_limits<unsigned>::max())
      return MemoryLocation::getBeforeOrAfter(Region.pointer);
    return MemoryLocation(Region.pointer, LocationSize::precise(Region.length));
  };

  AAResults &AA = getAA(*queryFunction);
  return AA.isNoAlias(getLocation(*this), getLocation(R));
}

bool Region::oracleProvesNoAlias(Region &R) {
  if (!Oracle || !hasCompleteOracleEvidence() || !R.hasCompleteOracleEvidence()) {
    if (OracleFallbackCount)
      ++*OracleFallbackCount;
    return false;
  }

  if (hasSVFTopEvidence() || R.hasSVFTopEvidence()) {
    if (OracleMayAliasCount)
      ++*OracleMayAliasCount;
    return false;
  }

  for (const auto &leftRegion : evidenceRegionIds) {
    if (R.evidenceRegionIds.count(leftRegion)) {
      if (OracleMayAliasCount)
        ++*OracleMayAliasCount;
      return false;
    }
  }

  if (OracleNoAliasCount)
    ++*OracleNoAliasCount;
  return true;
}

bool Region::hasCompleteOracleEvidence() const {
  if (oracleIncomplete)
    return false;

  if (accessEvidence.empty() || evidenceRegionIds.empty())
    return false;

  return true;
}

bool Region::oracleEvidenceDisjointFrom(
    const MemoryPartitionOracle::RegionSet &regionIds) const {
  if (!hasCompleteOracleEvidence())
    return false;

  if (regionIds.count(SVFMemoryPartition::TopRegion))
    return false;

  for (const auto &regionId : evidenceRegionIds)
    if (regionId == SVFMemoryPartition::TopRegion || regionIds.count(regionId))
      return false;

  return true;
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
  oracleIncomplete = oracleIncomplete || R.oracleIncomplete;
  type = (bytewise || collapse) ? nullptr : type;
  accessEvidence.insert(accessEvidence.end(), R.accessEvidence.begin(),
                        R.accessEvidence.end());
  evidenceRegionIds.insert(R.evidenceRegionIds.begin(),
                           R.evidenceRegionIds.end());
}

bool Region::dsaFallbackOverlaps(Region &R) {
  const bool cellRefined =
      SmackOptions::MemoryPartitioner.getValue() == "cell-refined";
  const bool complicatedOverlap =
      complicated && R.complicated &&
      (!cellRefined || !representative || !R.representative ||
       representative == R.representative);
  return (incomplete && R.incomplete) || complicatedOverlap ||
         (representative == R.representative &&
          (collapsed || !isDisjoint(R.offset, R.length)));
}

bool Region::overlaps(Region &R) {
  if (isSVFNativePartitioner()) {
    if (!hasCompleteOracleEvidence() || !R.hasCompleteOracleEvidence()) {
      report_fatal_error(
          "svf-native cannot compare regions without complete SVF evidence",
          false);
    }

    if (evidenceRegionIds.count(SVFMemoryPartition::TopRegion) ||
        R.evidenceRegionIds.count(SVFMemoryPartition::TopRegion)) {
      if (OracleMayAliasCount)
        ++*OracleMayAliasCount;
      return true;
    }

    for (const auto &leftRegion : evidenceRegionIds) {
      if (R.evidenceRegionIds.count(leftRegion)) {
        if (OracleMayAliasCount)
          ++*OracleMayAliasCount;
        return true;
      }
    }

    if (OracleNoAliasCount)
      ++*OracleNoAliasCount;
    return false;
  }

  return dsaFallbackOverlaps(R);
}

bool Region::overlaps(Region &R,
                      llvm::function_ref<llvm::AAResults &(Function &)> getAA) {
  const bool aaRefined = usesAARefinementPartitioner();
  const bool svfRefined = isSVFRefinedPartitioner();
  const bool baseOverlap = overlaps(R);

  if (!baseOverlap)
    return false;

  if (svfRefined && oracleProvesNoAlias(R))
    return false;

  if (aaRefined && aaProvesNoAlias(R, getAA))
    return false;
  return baseOverlap;
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
  if (!SmackOptions::NoMemoryRegionSplitting && !isSVFNativePartitioner()) {
    AU.addRequired<DSAWrapper>();
    if (usesAARefinementPartitioner())
      AU.addRequired<AAResultsWrapperPass>();
  }
}

void Regions::runImpl(Module &M, DSAWrapper &dsa) {
  auto noAA = [](Function &) -> AAResults & {
    llvm_unreachable("AA getter is unavailable");
  };
  runImpl(M, dsa, noAA);
}

void Regions::runImpl(
    Module &M, DSAWrapper &dsa,
    std::function<llvm::AAResults &(Function &)> getAA) {
  finalized = false;
  regions.clear();
  clearSVFRegionIndex();
  accessCount = 0;
  mergeCount = 0;
  lateRegionCount = 0;
  oracleNoAliasCount = 0;
  oracleMayAliasCount = 0;
  oracleFallbackCount = 0;
  oracleFrameCompleteCount = 0;
  oracleFrameFallbackCount = 0;
  oracleFrameExcludedMapCount = 0;
  oracleFrameRetainedMapCount = 0;
  svfLoopFrameCompleteCount = 0;
  svfLoopFrameFallbackCount = 0;
  svfLoopFrameInvariantCount = 0;
  svfLoopFrameExcludedMapCount = 0;
  svfLoopFrameRetainedMapCount = 0;
  dsaMode = dsa.analysisKindName();
  aaGetter = getAA;
  hasAAGetter = usesOverlapRefinementPartitioner();
  oracle.reset();
  svfPartition.reset();
  if (!SmackOptions::NoMemoryRegionSplitting) {
    if (usesExternalOraclePartitioner())
      oracle = MemoryPartitionOracle::loadFromFile(
          SmackOptions::MemoryPartitionOracle.getValue(), M);
    Region::init(M, dsa, oracle.get(), &oracleNoAliasCount,
                 &oracleMayAliasCount, &oracleFallbackCount);
    visit(M);
  }
  hasAAGetter = false;
  finalized = true;
}

void Regions::runImpl(Module &M) {
  finalized = false;
  regions.clear();
  clearSVFRegionIndex();
  accessCount = 0;
  mergeCount = 0;
  lateRegionCount = 0;
  oracleNoAliasCount = 0;
  oracleMayAliasCount = 0;
  oracleFallbackCount = 0;
  oracleFrameCompleteCount = 0;
  oracleFrameFallbackCount = 0;
  oracleFrameExcludedMapCount = 0;
  oracleFrameRetainedMapCount = 0;
  svfLoopFrameCompleteCount = 0;
  svfLoopFrameFallbackCount = 0;
  svfLoopFrameInvariantCount = 0;
  svfLoopFrameExcludedMapCount = 0;
  svfLoopFrameRetainedMapCount = 0;
  dsaMode = "none";
  aaGetter = nullptr;
  hasAAGetter = false;
  oracle.reset();
  svfPartition.reset();
  if (!SmackOptions::NoMemoryRegionSplitting) {
    if (isSVFNativePartitioner()) {
      svfPartition = SVFMemoryPartition::build(M);
      Region::init(M, svfPartition.get(), &oracleNoAliasCount,
                   &oracleMayAliasCount, &oracleFallbackCount);
    } else if (usesExternalOraclePartitioner()) {
      oracle = MemoryPartitionOracle::loadFromFile(
          SmackOptions::MemoryPartitionOracle.getValue(), M);
      Region::init(M, oracle.get(), &oracleNoAliasCount, &oracleMayAliasCount,
                   &oracleFallbackCount);
    } else {
      report_fatal_error("internal error: DSA-backed Regions run without DSA",
                         false);
    }
    visit(M);
  }
  finalized = true;
}

bool Regions::runOnModule(Module &M) {
  finalized = false;
  regions.clear();
  clearSVFRegionIndex();
  accessCount = 0;
  mergeCount = 0;
  lateRegionCount = 0;
  oracleNoAliasCount = 0;
  oracleMayAliasCount = 0;
  oracleFallbackCount = 0;
  oracleFrameCompleteCount = 0;
  oracleFrameFallbackCount = 0;
  oracleFrameExcludedMapCount = 0;
  oracleFrameRetainedMapCount = 0;
  svfLoopFrameCompleteCount = 0;
  svfLoopFrameFallbackCount = 0;
  svfLoopFrameInvariantCount = 0;
  svfLoopFrameExcludedMapCount = 0;
  svfLoopFrameRetainedMapCount = 0;
  dsaMode = "none";
  oracle.reset();
  svfPartition.reset();
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
    if (isSVFNativePartitioner()) {
      svfPartition = SVFMemoryPartition::build(M);
      Region::init(M, svfPartition.get(), &oracleNoAliasCount,
                   &oracleMayAliasCount, &oracleFallbackCount);
      dsaMode = "none";
      hasAAGetter = false;
    } else {
      DSAWrapper &dsa = getAnalysis<DSAWrapper>();
      if (usesExternalOraclePartitioner())
        oracle = MemoryPartitionOracle::loadFromFile(
            SmackOptions::MemoryPartitionOracle.getValue(), M);
      Region::init(M, dsa, oracle.get(), &oracleNoAliasCount,
                   &oracleMayAliasCount, &oracleFallbackCount);
      dsaMode = Region::getDSA()->analysisKindName();
      hasAAGetter = usesOverlapRefinementPartitioner();
      if (usesAARefinementPartitioner())
        aaGetter = [this](Function &F) -> AAResults & {
          return getAnalysis<AAResultsWrapperPass>(F).getAAResults();
        };
      else if (hasAAGetter)
        aaGetter = [](Function &) -> AAResults & {
          llvm_unreachable("AA getter is unavailable");
        };
    }
    visit(M);
  }

  hasAAGetter = false;
  finalized = true;
  return false;
}

llvm::AnalysisKey RegionsAnalysis::Key;

RegionsAnalysis::Result
RegionsAnalysis::run(Module &M, llvm::ModuleAnalysisManager &MAM) {
  RegionsResult r;
  r.regions = std::make_unique<Regions>();
  if (!SmackOptions::NoMemoryRegionSplitting) {
    if (isSVFNativePartitioner()) {
      r.regions->runImpl(M);
    } else {
      auto &dsa = MAM.getResult<DSAWrapperAnalysis>(M);
      auto &FAM = MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
                      .getManager();
      r.regions->runImpl(M, *dsa.wrapper, [&FAM](Function &F) -> AAResults & {
        return FAM.getResult<AAManager>(F);
      });
    }
  }
  return r;
}

unsigned Regions::size() const { return regions.size(); }

Region &Regions::get(unsigned R) { return regions[R]; }

void Regions::clearSVFRegionIndex() { svfRegionIndex.clear(); }

void Regions::indexSVFRegion(unsigned region) {
  if (region >= regions.size())
    return;
  for (const auto &regionId : regions[region].getEvidenceRegionIds())
    svfRegionIndex[regionId].insert(region);
}

void Regions::rebuildSVFRegionIndex() {
  clearSVFRegionIndex();
  for (unsigned i = 0; i < regions.size(); ++i)
    indexSVFRegion(i);
}

std::set<unsigned> Regions::svfOverlapCandidates(const Region &region) const {
  std::set<unsigned> candidates;
  if (region.hasSVFTopEvidence()) {
    for (unsigned i = 0; i < regions.size(); ++i)
      candidates.insert(i);
    return candidates;
  }

  auto top = svfRegionIndex.find(SVFMemoryPartition::TopRegion);
  if (top != svfRegionIndex.end())
    candidates.insert(top->second.begin(), top->second.end());

  for (const auto &regionId : region.getEvidenceRegionIds()) {
    auto it = svfRegionIndex.find(regionId);
    if (it != svfRegionIndex.end())
      candidates.insert(it->second.begin(), it->second.end());
  }
  return candidates;
}

std::set<unsigned>
Regions::refinedOverlapCandidates(const Region &region) const {
  std::set<unsigned> candidates;
  if (!isSVFRefinedPartitioner() || !region.hasCompleteOracleEvidence()) {
    for (unsigned i = 0; i < regions.size(); ++i)
      candidates.insert(i);
    return candidates;
  }

  candidates = svfOverlapCandidates(region);
  for (unsigned i = 0; i < regions.size(); ++i)
    if (!regions[i].hasCompleteOracleEvidence())
      candidates.insert(i);
  return candidates;
}

void Regions::recordOracleFrameDecision(bool complete, unsigned excludedMaps,
                                        unsigned retainedMaps) {
  if (complete)
    ++oracleFrameCompleteCount;
  else
    ++oracleFrameFallbackCount;
  oracleFrameExcludedMapCount += excludedMaps;
  oracleFrameRetainedMapCount += retainedMaps;
}

void Regions::recordSVFLoopFrameDecision(bool complete, unsigned excludedMaps,
                                         unsigned retainedMaps) {
  if (complete)
    ++svfLoopFrameCompleteCount;
  else
    ++svfLoopFrameFallbackCount;
  svfLoopFrameInvariantCount += excludedMaps;
  svfLoopFrameExcludedMapCount += excludedMaps;
  svfLoopFrameRetainedMapCount += retainedMaps;
}

void Regions::snapshotReport(SmackMemoryPartitionReport &report) const {
  report.partitioner = SmackOptions::MemoryPartitioner.getValue();
  report.dsaMode = dsaMode;
  report.regionCount = regions.size();
  report.memoryAccessCount = accessCount;
  report.mergeCount = mergeCount;
  report.lateRegionCount = lateRegionCount;
  report.singletonCount = 0;
  report.allocatedCount = 0;
  report.bytewiseCount = 0;
  report.incompleteCount = 0;
  report.complicatedCount = 0;
  report.collapsedCount = 0;
  report.typedCount = 0;
  report.untypedCount = 0;
  const MemoryPartitionOracle *activeOracle = getOracle();
  report.oracleAccessCount = activeOracle ? activeOracle->accessCount() : 0;
  report.oracleCallsiteEffectCount =
      activeOracle ? activeOracle->callsiteEffectCount() : 0;
  report.oracleFunctionEffectCount =
      activeOracle ? activeOracle->functionEffectCount() : 0;
  report.oracleLoopEffectCount = activeOracle ? activeOracle->loopEffectCount() : 0;
  report.oracleIndirectCallTargetCount =
      activeOracle ? activeOracle->indirectCallTargetCount() : 0;
  report.oracleNoAliasCount = oracleNoAliasCount;
  report.oracleMayAliasCount = oracleMayAliasCount;
  report.oracleFallbackCount = oracleFallbackCount;
  report.oracleFrameCompleteCount = oracleFrameCompleteCount;
  report.oracleFrameFallbackCount = oracleFrameFallbackCount;
  report.oracleFrameExcludedMapCount = oracleFrameExcludedMapCount;
  report.oracleFrameRetainedMapCount = oracleFrameRetainedMapCount;
  report.svfLoopFrameCompleteCount = svfLoopFrameCompleteCount;
  report.svfLoopFrameFallbackCount = svfLoopFrameFallbackCount;
  report.svfLoopFrameInvariantCount = svfLoopFrameInvariantCount;
  report.svfLoopFrameExcludedMapCount = svfLoopFrameExcludedMapCount;
  report.svfLoopFrameRetainedMapCount = svfLoopFrameRetainedMapCount;

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
    if (!isSVFNativePartitioner() && !region.hasRepresentative())
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
  ++accessCount;

  SDEBUG(errs() << "[regions]   using region: ");
  SDEBUG(R.print(errs()));
  SDEBUG(errs() << "\n");

  if (isSVFNativePartitioner()) {
    auto candidates = svfOverlapCandidates(R);

    if (finalized) {
      for (unsigned candidate : candidates) {
        if (candidate < regions.size() &&
            (hasAAGetter ? regions[candidate].overlaps(R, aaGetter)
                         : regions[candidate].overlaps(R))) {
          SDEBUG(errs() << "[regions]   found finalized SVF overlap at index "
                        << candidate << "\n\n");
          return candidate;
        }
      }

      if (!regions.empty())
        ++oracleNoAliasCount;
      regions.emplace_back(R);
      r = regions.size() - 1;
      indexSVFRegion(r);
      ++lateRegionCount;
      SDEBUG(errs() << "[regions]   appended finalized SVF region at index "
                    << r << "\n\n");
      return r;
    }

    r = regions.size();
    for (unsigned candidate : candidates) {
      if (candidate < regions.size() &&
          (hasAAGetter ? regions[candidate].overlaps(R, aaGetter)
                       : regions[candidate].overlaps(R))) {
        r = candidate;
        break;
      }
    }

    if (r == regions.size()) {
      if (!regions.empty())
        ++oracleNoAliasCount;
      regions.emplace_back(R);
      indexSVFRegion(r);
      SDEBUG(errs() << "[regions]   appended SVF region at index " << r
                    << "\n\n");
      return r;
    }

    regions[r].merge(R);
    ++mergeCount;
    indexSVFRegion(r);

    bool merged = true;
    while (merged) {
      merged = false;
      auto transitive = svfOverlapCandidates(regions[r]);
      for (unsigned q : transitive) {
        if (q >= regions.size() || q == r)
          continue;
        if (hasAAGetter ? regions[r].overlaps(regions[q], aaGetter)
                        : regions[r].overlaps(regions[q])) {
          regions[r].merge(regions[q]);
          ++mergeCount;
          regions.erase(regions.begin() + q);
          if (q < r)
            --r;
          rebuildSVFRegionIndex();
          merged = true;
          break;
        }
      }
    }

    SDEBUG(errs() << "[regions]   returning SVF index: " << r << "\n\n");
    return r;
  }

  if (finalized) {
    auto candidates = refinedOverlapCandidates(R);
    for (unsigned candidate : candidates) {
      if (candidate < regions.size() &&
          (hasAAGetter ? regions[candidate].overlaps(R, aaGetter)
                       : regions[candidate].overlaps(R))) {
        SDEBUG(errs() << "[regions]   found finalized overlap at index "
                      << candidate << "\n\n");
        return candidate;
      }
    }

    r = regions.size();
    regions.emplace_back(R);
    if (isSVFRefinedPartitioner())
      indexSVFRegion(r);
    ++lateRegionCount;
    SDEBUG(errs() << "[regions]   appended finalized region at index " << r
                  << "\n\n");
    return r;
  }

  auto candidates = refinedOverlapCandidates(R);
  r = regions.size();
  for (unsigned candidate : candidates) {
    if (candidate < regions.size() &&
        (hasAAGetter ? regions[candidate].overlaps(R, aaGetter)
                     : regions[candidate].overlaps(R))) {
      r = candidate;

      SDEBUG(errs() << "[regions]   found overlap at index " << r << ": ");
      SDEBUG(regions[r].print(errs()));
      SDEBUG(errs() << "\n");

      regions[r].merge(R);
      ++mergeCount;

      SDEBUG(errs() << "[regions]   merged region: ");
      SDEBUG(regions[r].print(errs()));
      SDEBUG(errs() << "\n");

      break;
    }
  }

  if (r == regions.size()) {
    regions.emplace_back(R);
    if (isSVFRefinedPartitioner())
      indexSVFRegion(r);

  } else {
    if (isSVFRefinedPartitioner())
      indexSVFRegion(r);
    // Here is the tricky part: in case R was merged with an existing region,
    // we must now also merge any other region which intersects with R.
    if (isSVFRefinedPartitioner()) {
      bool merged = true;
      while (merged) {
        merged = false;
        auto transitive = refinedOverlapCandidates(regions[r]);
        for (unsigned q : transitive) {
          if (q >= regions.size() || q == r)
            continue;
          if (hasAAGetter ? regions[r].overlaps(regions[q], aaGetter)
                          : regions[r].overlaps(regions[q])) {
            SDEBUG(errs() << "[regions]   found extra overlap at index " << q
                          << ": ");
            SDEBUG(regions[q].print(errs()));
            SDEBUG(errs() << "\n");

            regions[r].merge(regions[q]);
            ++mergeCount;
            regions.erase(regions.begin() + q);
            if (q < r)
              --r;
            rebuildSVFRegionIndex();

            SDEBUG(errs() << "[regions]   merged region: ");
            SDEBUG(regions[r].print(errs()));
            SDEBUG(errs() << "\n");

            merged = true;
            break;
          }
        }
      }
    } else {
      unsigned q = r + 1;
      while (q < regions.size()) {
        if (hasAAGetter ? regions[r].overlaps(regions[q], aaGetter)
                        : regions[r].overlaps(regions[q])) {

          SDEBUG(errs() << "[regions]   found extra overlap at index " << q
                        << ": ");
          SDEBUG(regions[q].print(errs()));
          SDEBUG(errs() << "\n");

          regions[r].merge(regions[q]);
          ++mergeCount;
          regions.erase(regions.begin() + q);

          SDEBUG(errs() << "[regions]   merged region: ");
          SDEBUG(regions[r].print(errs()));
          SDEBUG(errs() << "\n");

        } else {
          q++;
        }
      }
    }
  }

  SDEBUG(errs() << "[regions]   returning index: " << r << "\n\n");

  return r;
}

void Regions::visitLoadInst(LoadInst &I) {
  idx(I);
}

void Regions::visitStoreInst(StoreInst &I) {
  idx(I);
}

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
      const Type *T = legacyPointerElementType(P);
      if (!T && !SmackOptions::NoMemoryRegionSplitting && Region::getDSA())
        // Region::getDSA() returns the shared static set by Region::init(M, dsa);
        // both legacy Regions::runOnModule and RegionsAnalysis populate it.
        T = Region::getDSA()->getPointedType(P);
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
