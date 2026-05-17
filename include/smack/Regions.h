//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REGIONS_H
#define REGIONS_H

#include "smack/MemoryPartitionOracle.h"
#include "smack/SVFMemoryPartition.h"
#include "seadsa/Graph.hh"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/ADT/STLFunctionalExtras.h"

#include <functional>
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

using namespace llvm;

namespace llvm {
class AAResults;
class DSNode;
class LoadInst;
class StoreInst;
}

namespace smack {

class DSAWrapper;
struct SmackMemoryPartitionReport;

struct MemoryAccessEvidence {
  std::string key;
  std::vector<std::string> regionIds;
};

class Region {
private:
  LLVMContext *context;
  const Value *pointer;
  Function *function;
  const seadsa::Node *representative;
  const Type *type;
  unsigned offset;
  unsigned length;
  std::vector<MemoryAccessEvidence> accessEvidence;
  MemoryPartitionOracle::RegionSet evidenceRegionIds;
  bool oracleIncomplete;

  bool singleton;
  bool allocated;
  bool bytewise;
  bool incomplete;
  bool complicated;
  bool collapsed;

  static const DataLayout *DL;
  static const MemoryPartitionOracle *Oracle;
  static unsigned *OracleNoAliasCount;
  static unsigned *OracleMayAliasCount;
  static unsigned *OracleFallbackCount;
  // DSA is the shared sea-dsa wrapper. Public so Regions::visit* methods +
  // RegionsAnalysis can access it without going through Pass::getAnalysis.
public:
  static DSAWrapper *getDSA() { return DSA; }
private:
  static DSAWrapper *DSA;
  static const SVFMemoryPartition *SVFPartition;

  static bool isSingleton(const llvm::Value *v, unsigned length);
  static bool isAllocated(const seadsa::Node *N);
  static bool isComplicated(const seadsa::Node *N);

  void init(const Value *V, const Type *accessType, unsigned length,
            bool addNativePointerEvidenceForValue = true);
  void addAccessEvidence(const llvm::Instruction &I);
  void addNativePointerEvidence(const llvm::Value &V);
  void addNativeEvidence(llvm::StringRef key,
                         const SVFMemoryPartition::Evidence &evidence);
  bool isDisjoint(unsigned offset, unsigned length);
  bool dsaFallbackOverlaps(Region &R);
  bool aaProvesNoAlias(
      Region &R, llvm::function_ref<llvm::AAResults &(Function &)> getAA);
  bool oracleProvesNoAlias(Region &R);

public:
  Region(const Value *V);
  Region(const Value *V, unsigned length);
  Region(const Value *V, const Type *accessType);
  Region(const Value *V, const Type *accessType, unsigned length);
  Region(const llvm::LoadInst &I);
  Region(const llvm::StoreInst &I);

  static void init(Module &M, Pass &P);
  // NewPM-friendly overload: caller supplies the DSAWrapper directly (e.g.
  // from DSAWrapperAnalysis result) instead of going through Pass::getAnalysis.
  static void init(Module &M, DSAWrapper &dsa);
  static void init(Module &M, DSAWrapper &dsa,
                   const MemoryPartitionOracle *oracle,
                   unsigned *oracleNoAliasCount,
                   unsigned *oracleMayAliasCount,
                   unsigned *oracleFallbackCount);
  static void init(Module &M, const MemoryPartitionOracle *oracle,
                   unsigned *oracleNoAliasCount,
                   unsigned *oracleMayAliasCount,
                   unsigned *oracleFallbackCount);
  static void init(Module &M, const SVFMemoryPartition *svfPartition,
                   unsigned *oracleNoAliasCount,
                   unsigned *oracleMayAliasCount,
                   unsigned *oracleFallbackCount);

  void merge(Region &R);
  bool overlaps(Region &R);
  bool overlaps(Region &R,
                llvm::function_ref<llvm::AAResults &(Function &)> getAA);

  bool isSingleton() const { return singleton; };
  bool isAllocated() const { return allocated; };
  bool bytewiseAccess() const { return bytewise; }
  bool isIncomplete() const { return incomplete; }
  bool isComplicated() const { return complicated; }
  bool isCollapsed() const { return collapsed; }
  bool hasRepresentative() const { return representative != nullptr; }
  const Type *getType() const { return type; }
  const MemoryPartitionOracle::RegionSet &getEvidenceRegionIds() const {
    return evidenceRegionIds;
  }
  bool hasSVFTopEvidence() const {
    return evidenceRegionIds.count(SVFMemoryPartition::TopRegion) != 0;
  }
  bool hasCompleteOracleEvidence() const;
  bool oracleEvidenceDisjointFrom(
      const MemoryPartitionOracle::RegionSet &regionIds) const;

  void print(raw_ostream &);
};

class Regions : public ModulePass, public InstVisitor<Regions> {
private:
  std::vector<Region> regions;
  std::unordered_map<std::string, std::set<unsigned>> svfRegionIndex;
  bool finalized;
  unsigned accessCount;
  unsigned mergeCount;
  unsigned lateRegionCount;
  unsigned oracleNoAliasCount;
  unsigned oracleMayAliasCount;
  unsigned oracleFallbackCount;
  unsigned oracleFrameCompleteCount;
  unsigned oracleFrameFallbackCount;
  unsigned oracleFrameExcludedMapCount;
  unsigned oracleFrameRetainedMapCount;
  unsigned svfLoopFrameCompleteCount;
  unsigned svfLoopFrameFallbackCount;
  unsigned svfLoopFrameInvariantCount;
  unsigned svfLoopFrameExcludedMapCount;
  unsigned svfLoopFrameRetainedMapCount;
  std::string dsaMode;
  std::unique_ptr<MemoryPartitionOracle> oracle;
  std::unique_ptr<SVFMemoryPartition> svfPartition;
  std::function<llvm::AAResults &(Function &)> aaGetter;
  bool hasAAGetter;

  void clearSVFRegionIndex();
  void indexSVFRegion(unsigned region);
  void rebuildSVFRegionIndex();
  std::set<unsigned> svfOverlapCandidates(const Region &region) const;
  std::set<unsigned> refinedOverlapCandidates(const Region &region) const;
  unsigned idx(Region &R);

public:
  static char ID;
  Regions()
      : ModulePass(ID), finalized(false), accessCount(0), mergeCount(0),
        lateRegionCount(0), oracleNoAliasCount(0), oracleMayAliasCount(0),
        oracleFallbackCount(0), oracleFrameCompleteCount(0),
        oracleFrameFallbackCount(0), oracleFrameExcludedMapCount(0),
        oracleFrameRetainedMapCount(0), svfLoopFrameCompleteCount(0),
        svfLoopFrameFallbackCount(0), svfLoopFrameInvariantCount(0),
        svfLoopFrameExcludedMapCount(0), svfLoopFrameRetainedMapCount(0),
        dsaMode("unknown"), oracle(nullptr), svfPartition(nullptr),
        aaGetter(nullptr), hasAAGetter(false) {}
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  virtual bool runOnModule(llvm::Module &M) override;

  unsigned size() const;
  unsigned idx(const llvm::Value *v);
  unsigned idx(const llvm::Value *v, unsigned length);
  unsigned idx(const llvm::Value *v, const llvm::Type *accessType);
  unsigned idx(const llvm::Value *v, const llvm::Type *accessType,
               unsigned length);
  unsigned idx(const llvm::LoadInst &I);
  unsigned idx(const llvm::StoreInst &I);
  Region &get(unsigned R);
  const MemoryPartitionOracle *getOracle() const {
    if (oracle)
      return oracle.get();
    return svfPartition ? svfPartition->getOracle() : nullptr;
  }
  void recordOracleFrameDecision(bool complete, unsigned excludedMaps,
                                 unsigned retainedMaps);
  void recordSVFLoopFrameDecision(bool complete, unsigned excludedMaps,
                                  unsigned retainedMaps);
  void snapshotReport(SmackMemoryPartitionReport &report) const;

  // void visitModule(Module& M) {
  //   for (const GlobalValue& G : M.globals())
  //     collect(&G);
  // }

  // void visitAllocaInst(AllocaInst& I) {
  // getRegion(&I);
  // }

  void visitLoadInst(LoadInst &);
  void visitStoreInst(StoreInst &);
  void visitAtomicCmpXchgInst(AtomicCmpXchgInst &);
  void visitAtomicRMWInst(AtomicRMWInst &);
  void visitMemSetInst(MemSetInst &);
  void visitMemTransferInst(MemTransferInst &);
  void visitCallInst(CallInst &);

  // Shared body used by both legacy runOnModule + NewPM RegionsAnalysis.
  // Caller supplies the DSAWrapper.
  void runImpl(llvm::Module &M, DSAWrapper &dsa);
  void runImpl(llvm::Module &M, DSAWrapper &dsa,
               std::function<llvm::AAResults &(Function &)> getAA);
  void runImpl(llvm::Module &M);
};

// NewPM ModuleAnalysis returning a populated `Regions` instance. Uses
// `DSAWrapperAnalysis` for DSA-backed partitioners and skips it for
// `svf-native`.
struct RegionsResult {
  std::unique_ptr<Regions> regions;
  Regions *operator->() { return regions.get(); }
  Regions &operator*() { return *regions; }
  // Sticky cache: DSA-backed Regions hold raw seadsa::Node* into DSAWrapper
  // state. Re-running RegionsAnalysis between consumers would invalidate the
  // referenced nodes; never invalidate the cached result.
  bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                  llvm::ModuleAnalysisManager::Invalidator &) {
    return false;
  }
};

class RegionsAnalysis : public llvm::AnalysisInfoMixin<RegionsAnalysis> {
  friend llvm::AnalysisInfoMixin<RegionsAnalysis>;
  static llvm::AnalysisKey Key;

public:
  using Result = RegionsResult;
  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

} // namespace smack

#endif // REGIONS_H
