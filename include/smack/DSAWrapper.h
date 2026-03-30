//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE for details.
//
#ifndef DSAWRAPPER_H
#define DSAWRAPPER_H

#include <unordered_map>
#include <unordered_set>

#include "seadsa/DsaAnalysis.hh"
#include "seadsa/Global.hh"
#include "seadsa/Graph.hh"

namespace smack {

class DSAWrapper : public llvm::ModulePass {
private:
  llvm::Module *module;
  seadsa::GlobalAnalysis *SD;
  // Fallback graph for globals/constants (entry function's graph).
  seadsa::Graph *DG;
  std::unordered_set<const seadsa::Node *> staticInits;
  std::unordered_set<const llvm::Value *> memOpds;
  // Mapping from the DSNodes associated with globals to the numbers of
  // globals associated with them.
  std::unordered_map<const seadsa::Node *, unsigned> globalRefCount;
  const llvm::DataLayout *dataLayout;

  void collectStaticInits(llvm::Module &M);
  void collectMemOpds(llvm::Module &M);
  void countGlobalRefs();

  // Resolve the appropriate DSA graph for a given value based on its
  // enclosing function. Falls back to DG for globals/constants.
  seadsa::Graph &getGraphForValue(const llvm::Value *v);

public:
  static char ID;
  DSAWrapper() : ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  virtual bool runOnModule(llvm::Module &M) override;

  bool isStaticInitd(const seadsa::Node *n);
  bool isMemOpd(const llvm::Value *v);
  bool isRead(const llvm::Value *V);
  bool isSingletonGlobal(const llvm::Value *V);
  unsigned getPointedTypeSize(const llvm::Value *v);
  unsigned getOffset(const llvm::Value *v);
  unsigned getOffset(const llvm::Value *v, const llvm::Function &F);
  const seadsa::Node *getNode(const llvm::Value *v);
  const seadsa::Node *getNode(const llvm::Value *v, const llvm::Function &F);
  bool isTypeSafe(const llvm::Value *v);
  bool isTypeSafe(const llvm::Value *v, const llvm::Function &F);
  unsigned getNumGlobals(const seadsa::Node *n);

  // Per-function graph access for context-sensitive analysis.
  seadsa::Graph &getGraph(const llvm::Function &F);
  bool hasGraph(const llvm::Function &F) const;
};
} // namespace smack

#endif // DSAWRAPPER_H
