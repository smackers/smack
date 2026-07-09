//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REGIONS_H
#define REGIONS_H

#include "seadsa/Graph.hh"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Pass.h"

#include <map>
#include <set>

using namespace llvm;

namespace llvm {
class DSNode;
}

namespace smack {

class DSAWrapper;

class Region {
private:
  LLVMContext *context;
  const seadsa::Node *representative;
  const Type *type;
  unsigned offset;
  unsigned length;

  bool singleton;
  bool allocated;
  bool bytewise;
  bool incomplete;
  bool complicated;
  bool collapsed;
  bool globalScope;

  static const DataLayout *DL;
  static DSAWrapper *DSA;

  static bool isSingleton(const llvm::Value *v, unsigned length,
                          const llvm::Function *F);
  static bool isAllocated(const seadsa::Node *N);
  static bool isComplicated(const seadsa::Node *N);

  void init(const Value *V, unsigned length, const llvm::Function *F);
  bool isDisjoint(unsigned offset, unsigned length);

public:
  Region(const Value *V, const llvm::Function *F);
  Region(const Value *V, const llvm::Function *F, unsigned length);
  Region(const seadsa::Node *node, LLVMContext &ctx);
  Region(const seadsa::Node *node, unsigned offset, unsigned length,
         LLVMContext &ctx);
  Region(const seadsa::Node *node, unsigned offset, unsigned length,
         const llvm::Type *type, bool bytewise, LLVMContext &ctx);

  static void init(Module &M, Pass &P);

  // Returns true if the merge changed this region (extent or attributes).
  bool merge(Region &R);
  // Absorb R's attributes (type, bytewise, flags) without widening this
  // region's extent, so that this region's declared map type covers
  // accesses performed through R.
  void mergeAttributes(const Region &R);
  bool overlaps(Region &R);

  bool isSingleton() const { return singleton; };
  bool isAllocated() const { return allocated; };
  bool bytewiseAccess() const { return bytewise; }
  bool isGlobalScope() const { return globalScope; }
  // Force module-level emission (used when another function's region is
  // unified with this one, so the map must be visible module-wide).
  void markGlobalScope() { globalScope = true; }
  const Type *getType() const { return type; }
  const seadsa::Node *getRepresentative() const { return representative; }
  unsigned getOffset() const { return offset; }
  unsigned getLength() const { return length; }

  void print(raw_ostream &);
};

struct FunctionRegionInfo {
  std::set<unsigned> readRegions;
  std::set<unsigned> modifiedRegions;
  std::set<unsigned> inputRegions;
  std::set<unsigned> outputRegions;
};

class Regions : public ModulePass, public InstVisitor<Regions> {
private:
  // Per-function region vectors (each function has its own local numbering).
  std::map<const llvm::Function *, std::vector<Region>> funcRegionVecs;

  // Regions that were forcibly merged because SeaDsa call-site mappings showed
  // they alias, but whose representatives differ from the canonical region.
  std::map<const llvm::Function *, std::vector<std::pair<Region, unsigned>>>
      mergedRegionAliases;

  // Per-function read/write sets (using function-local region indices).
  std::map<const llvm::Function *, FunctionRegionInfo> funcRegions;

  // Call-site mapping: callee region index -> caller region index.
  std::map<const llvm::CallBase *, std::map<unsigned, unsigned>>
      callSiteMappings;

  // For non-entry functions: mapping from their region indices to the entry
  // function's region indices (matched via globals and call-site mappings).
  std::map<const llvm::Function *, std::map<unsigned, unsigned>>
      globalMemoryMappings;

  // Module-level maps for memory shared across functions without touching
  // the entry function's regions (e.g., heap passed between siblings).
  std::vector<Region> sharedRegions;
  std::map<std::pair<const llvm::Function *, unsigned>, unsigned>
      sharedRegionIndex;

  static FunctionRegionInfo emptyRegionInfo;

  // The function currently being visited (set during visit phase).
  const llvm::Function *currentFunction = nullptr;

  // DSAWrapper pointer cached during runOnModule.
  DSAWrapper *DSA = nullptr;

  // Bumped on every region creation or merge; used to detect when a pass
  // over the module made structural changes that invalidate region indices.
  unsigned structuralVersion = 0;

  // Set once Phase 3 has converged: call-site mappings are no longer
  // recomputed, so information lost in later merges cannot be recovered.
  bool mappingsFinal = false;

  // Number of callee->caller associations dropped by key collisions in
  // remapAfterMerge after Phase 3 convergence (see the warning emitted in
  // runOnModule).
  unsigned droppedMappings = 0;

  // Per-function idx: find or create a region in F's vector.
  unsigned idx(Region &R, const llvm::Function *F);

  void computeCallSiteMappings(llvm::Module &M);
  void computeOneCallSiteMapping(llvm::CallBase *CI,
                                 const llvm::Function *caller,
                                 llvm::Function *callee);
  void propagateRegionMerges(llvm::Module &M);
  bool mergeCalleeRegion(const llvm::Function *F, unsigned keep,
                         unsigned remove);
  // Repair all index-based bookkeeping (access sets, call-site mappings,
  // merged-region aliases) after F's region `remove` was merged into `keep`
  // and erased from F's region vector. Requires keep < remove.
  void remapAfterMerge(const llvm::Function *F, unsigned keep, unsigned remove);
  void computeGlobalMemoryMappings(llvm::Module &M);
  void unifySharedRegions(llvm::Module &M);
  void computeFunctionRegions(llvm::Module &M);
  void computeInterfaceRegions(llvm::Module &M);

public:
  static char ID;
  Regions() : ModulePass(ID) {}
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  virtual bool runOnModule(llvm::Module &M) override;

  // Per-function region access.
  unsigned size(const llvm::Function *F) const;
  unsigned idx(const llvm::Value *v, const llvm::Function *F);
  unsigned idx(const llvm::Value *v, const llvm::Function *F, unsigned length);
  Region &get(const llvm::Function *F, unsigned R);

  const FunctionRegionInfo &
  getFunctionRegionInfo(const llvm::Function *F) const;
  std::set<unsigned> getAccessedRegions(const llvm::Function *F) const;
  const std::map<unsigned, unsigned> &
  getCallSiteMapping(const llvm::CallBase *CI) const;
  const std::map<unsigned, unsigned> &
  getGlobalMemoryMapping(const llvm::Function *F) const;
  // Shared (module-level) maps for cross-function memory that does not
  // reach the entry function's regions. Returns -1 if F's region r is not
  // backed by a shared map.
  int getSharedRegionIndex(const llvm::Function *F, unsigned r) const;
  unsigned numSharedRegions() const { return sharedRegions.size(); }
  Region &getShared(unsigned i) { return sharedRegions[i]; }

  void visitLoadInst(LoadInst &);
  void visitStoreInst(StoreInst &);
  void visitAtomicCmpXchgInst(AtomicCmpXchgInst &);
  void visitAtomicRMWInst(AtomicRMWInst &);
  void visitMemSetInst(MemSetInst &);
  void visitMemTransferInst(MemTransferInst &);
  // Covers CallInst and InvokeInst (InstVisitor delegates both here).
  void visitCallBase(CallBase &);
};
} // namespace smack

#endif // REGIONS_H
