//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE for details.
//
#ifndef DSAWRAPPER_H
#define DSAWRAPPER_H

#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/IR/InstVisitor.h"
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
  std::vector<const sea_dsa::Node *> staticInits;
  const llvm::DataLayout *dataLayout;

  std::vector<const sea_dsa::Node *> collectStaticInits(llvm::Module &M);

public:
  static char ID;
  DSAWrapper() : ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual bool runOnModule(llvm::Module &M);

  bool isStaticInitd(const sea_dsa::Node *n);
  bool isRead(const llvm::Value *V);
  bool isAlloced(const llvm::Value *v);
  bool isExternal(const llvm::Value *v);
  bool isSingletonGlobal(const llvm::Value *V);
  unsigned getPointedTypeSize(const llvm::Value *v);
  int getOffset(const llvm::Value *v);
  const sea_dsa::Node *getNode(const llvm::Value *v);
  void printDSAGraphs(const char *Filename);
  bool isTypeSafe(const llvm::Value *v);
};
} // namespace smack

#endif // DSAWRAPPER_H
