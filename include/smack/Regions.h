//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REGIONS_H
#define REGIONS_H

#include "smack/DSAWrapper.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

#include <functional>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;

namespace llvm {
class LoadInst;
class StoreInst;
} // namespace llvm

namespace smack {

class DSAWrapper;
struct SmackMemoryPartitionReport;

class Region {
private:
  LLVMContext *context;
  const Value *pointer;
  Function *function;
  MemNodeRef representative;
  const Type *type;
  unsigned offset;
  unsigned length;

  bool singleton;
  bool allocated;
  bool bytewise;
  bool incomplete;
  bool complicated;
  bool collapsed;

  static const DataLayout *DL;
  // DSA is the shared SVF-backed wrapper. Public accessor so Regions::visit*
  // methods + RegionsAnalysis can reach it without Pass::getAnalysis.
public:
  static DSAWrapper *getDSA() { return DSA; }

private:
  static DSAWrapper *DSA;

  static bool isSingleton(const llvm::Value *v, unsigned length);
  static bool isAllocated(MemNodeRef N);
  static bool isComplicated(MemNodeRef N);

  void init(const Value *V, const Type *accessType, unsigned length);
  bool isDisjoint(unsigned offset, unsigned length);

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

  void merge(Region &R);
  bool overlaps(Region &R);

  bool isSingleton() const { return singleton; };
  bool isAllocated() const { return allocated; };
  bool bytewiseAccess() const { return bytewise; }
  bool isIncomplete() const { return incomplete; }
  bool isComplicated() const { return complicated; }
  bool isCollapsed() const { return collapsed; }
  bool hasRepresentative() const { return representative != nullptr; }
  const Type *getType() const { return type; }

  void print(raw_ostream &);
};

class Regions : public ModulePass, public InstVisitor<Regions> {
private:
  std::vector<Region> regions;
  unsigned idx(Region &R);

public:
  static char ID;
  Regions() : ModulePass(ID) {}
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
};

// NewPM ModuleAnalysis returning a populated `Regions` instance. Uses
// `DSAWrapperAnalysis` for the SVF-backed DSAWrapper.
struct RegionsResult {
  std::unique_ptr<Regions> regions;
  Regions *operator->() { return regions.get(); }
  Regions &operator*() { return *regions; }
  // Sticky cache: Regions hold opaque MemNodeRefs into DSAWrapper state.
  // Re-running RegionsAnalysis between consumers would invalidate the
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
