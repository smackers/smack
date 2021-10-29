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
  // The ds graph since we're using the context-insensitive version which
  // results in one graph for the whole module.
  seadsa::Graph *DG;
  std::unordered_set<const seadsa::Node *> staticInits;
  std::unordered_set<const seadsa::Node *> memOpds;
  // Mapping from the DSNodes associated with globals to the numbers of
  // globals associated with them.
  std::unordered_map<const seadsa::Node *, unsigned> globalRefCount;
  const llvm::DataLayout *dataLayout;

  void collectStaticInits(llvm::Module &M);
  void collectMemOpds(llvm::Module &M);
  void countGlobalRefs();

public:
  static char ID;
  DSAWrapper() : ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  virtual bool runOnModule(llvm::Module &M) override;

  bool isStaticInitd(const seadsa::Node *n);
  bool isMemOpd(const seadsa::Node *n);
  bool isRead(const llvm::Value *V);
  bool isSingletonGlobal(const llvm::Value *V);
  unsigned getPointedTypeSize(const llvm::Value *v);
  unsigned getOffset(const llvm::Value *v);
  const seadsa::Node *getNode(const llvm::Value *v);
  bool isTypeSafe(const llvm::Value *v);
  unsigned getNumGlobals(const seadsa::Node *n);
};
} // namespace smack

#endif // DSAWRAPPER_H
