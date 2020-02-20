//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef REGIONS_H
#define REGIONS_H

#include "llvm/IR/InstVisitor.h"
#include "sea_dsa/Graph.hh"

using namespace llvm;

namespace llvm {
class DSNode;
}

namespace smack {

class DSAWrapper;

class Region {
private:
  LLVMContext *context;
  const sea_dsa::Node *representative;
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
  static DSAWrapper *DSA;

  static bool isSingleton(const sea_dsa::Node *N, unsigned offset, unsigned length);
  static bool isAllocated(const sea_dsa::Node *N);
  //static bool bytewiseAccess(const DSNode *N);
  static bool isComplicated(const sea_dsa::Node *N);

  void init(const Value *V, unsigned length);
  bool isDisjoint(unsigned offset, unsigned length);

public:
  Region(const Value *V);
  Region(const Value *V, unsigned length);

  static void init(Module &M, Pass &P);

  void merge(Region &R);
  bool overlaps(Region &R);

  bool isSingleton() const { return singleton; };
  bool isAllocated() const { return allocated; };
  bool bytewiseAccess() const { return bytewise; }
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
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual bool runOnModule(llvm::Module &M);

  unsigned size() const;
  unsigned idx(const llvm::Value *v);
  unsigned idx(const llvm::Value *v, unsigned length);
  Region &get(unsigned R);

  // void visitModule(Module& M) {
  //   for (const GlobalValue& G : M.globals())
  //     collect(&G);
  // }

  // void visitAllocaInst(AllocaInst& I) {
  // getRegion(&I);
  // }

  void visitLoadInst(LoadInst &);
  void visitStoreInst(StoreInst &);
  void visitMemCpyInst(MemCpyInst &I);
  void visistMemSetInst(MemSetInst &I);
  void visitAtomicCmpXchgInst(AtomicCmpXchgInst &);
  void visitAtomicRMWInst(AtomicRMWInst &);
  void visitMemIntrinsic(MemIntrinsic &);
  void visitCallInst(CallInst &);
};
} // namespace smack

#endif // REGIONS_H
