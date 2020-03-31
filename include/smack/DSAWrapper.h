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

#include "sea_dsa/DsaAnalysis.hh"
#include "sea_dsa/Global.hh"
#include "sea_dsa/Graph.hh"

namespace smack {

class DSAWrapper : public llvm::ModulePass {
private:
  llvm::Module *module;
  sea_dsa::GlobalAnalysis *SD;
  // The ds graph since we're using the context-insensitive version which
  // results in one graph for the whole module.
  sea_dsa::Graph *DG;
  std::unordered_set<const sea_dsa::Node *> staticInits;
  std::unordered_set<const sea_dsa::Node *> memOpds;
  // Mapping from the DSNodes associated with globals to the numbers of
  // globals associated with them.
  std::unordered_map<const sea_dsa::Node *, unsigned> globalRefCount;
  const llvm::DataLayout *dataLayout;

  void collectStaticInits(llvm::Module &M);
  void collectMemOpds(llvm::Module &M);
  void countGlobalRefs();

public:
  static char ID;
  DSAWrapper() : ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual bool runOnModule(llvm::Module &M);

  bool isStaticInitd(const sea_dsa::Node *n);
  bool isMemOpd(const sea_dsa::Node *n);
  bool isRead(const llvm::Value *V);
  bool isSingletonGlobal(const llvm::Value *V);
  unsigned getPointedTypeSize(const llvm::Value *v);
  unsigned getOffset(const llvm::Value *v);
  const sea_dsa::Node *getNode(const llvm::Value *v);
  bool isTypeSafe(const llvm::Value *v);
  unsigned getNumGlobals(const sea_dsa::Node *n);
};
} // namespace smack

#endif // DSAWRAPPER_H
