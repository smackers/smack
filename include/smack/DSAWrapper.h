//
// This file is distributed under the MIT License. See LICENSE for details.
//
// SVF-backed replacement for the old sea-dsa DSAWrapper. It produces a SOUND
// DISJOINT memory-region partition for SMACK's split-memory Boogie model from
// SVF's Andersen points-to analysis:
//
//   region(p) = the union-find component containing every object in pts(p).
//
// Two pointers placed in DISTINCT regions therefore have disjoint points-to
// sets and are PROVABLY non-aliasing — exactly the invariant the split-memory
// model needs to stay sound. (sea-dsa got disjointness natively from its
// unification model; SVF is inclusion-based, so we derive it via union-find.)
//
#ifndef DSAWRAPPER_H
#define DSAWRAPPER_H

#include <map>
#include <unordered_map>
#include <unordered_set>

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace SVF {
class SVFIR;
class Andersen;
class LLVMModuleSet;
} // namespace SVF

namespace smack {

// Opaque handle to a disjoint memory region. Distinct non-null refs are
// PROVABLY non-aliasing. nullptr means "no region" (e.g. undef / null pointer /
// a pointer SVF could not resolve to any object).
using MemNodeRef = const void *;

class DSAWrapper : public llvm::ModulePass {
private:
  llvm::Module *module = nullptr;
  const llvm::DataLayout *dataLayout = nullptr;

  SVF::SVFIR *pag = nullptr;
  SVF::Andersen *ander = nullptr;
  SVF::LLVMModuleSet *ms = nullptr;

  // Union-find over SVF object NodeIDs.
  std::map<unsigned, unsigned> ufParent;
  unsigned ufFind(unsigned x);
  void ufUnite(unsigned a, unsigned b);

  // Per-component (region) aggregate properties, keyed by component root.
  struct RegionInfo {
    bool allocated = false;   // contains a heap or stack (alloca) object
    bool complicated = false; // contains an unknown/external/blackhole object
    bool incomplete = false;  // points-to may be incomplete (unknown object)
    bool arrayLike = false;   // contains an array object
    bool staticInitd = false; // contains a global with an initializer
    bool memOpd = false;      // is a memcpy/memset operand
    unsigned numGlobals = 0;  // number of distinct global objects merged in
  };
  std::unordered_map<unsigned, RegionInfo> regionInfo; // root -> info
  std::unordered_set<unsigned> memOpdObjs;             // objs used by memcpy/memset

  // Cache: pointer Value -> component root + 1 (0 == no region).
  std::unordered_map<const llvm::Value *, unsigned> valueRootPlus1;

  void buildUnionFind(llvm::Module &M);
  void aggregateRegions();
  // Returns component root + 1 for the region of pointer v, or 0 if none.
  unsigned rootPlus1(const llvm::Value *v);
  static MemNodeRef encode(unsigned rootPlus1) {
    return reinterpret_cast<MemNodeRef>(static_cast<uintptr_t>(rootPlus1));
  }
  static unsigned decode(MemNodeRef n) {
    return static_cast<unsigned>(reinterpret_cast<uintptr_t>(n));
  }
  const RegionInfo *infoOf(MemNodeRef n);

public:
  static char ID;
  DSAWrapper() : ModulePass(ID) {}
  ~DSAWrapper() override;

  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  bool runOnModule(llvm::Module &M) override;

  // Pointer queries.
  MemNodeRef getNode(const llvm::Value *v);
  unsigned getOffset(const llvm::Value *v);
  unsigned getPointedTypeSize(const llvm::Value *v);
  bool isRead(const llvm::Value *v);
  bool isTypeSafe(const llvm::Value *v);

  // Region (node) queries.
  unsigned getNumGlobals(MemNodeRef n);
  bool isStaticInitd(MemNodeRef n);
  bool isMemOpd(MemNodeRef n);
  bool isAllocated(MemNodeRef n);  // heap || stack
  bool isComplicated(MemNodeRef n);
  bool isIncomplete(MemNodeRef n);
  bool isArray(MemNodeRef n);
  bool isCollapsed(MemNodeRef n);
};
} // namespace smack

#endif // DSAWRAPPER_H
