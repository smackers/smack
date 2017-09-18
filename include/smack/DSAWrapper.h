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

namespace llvm {
class DSNode;
class DSGraph;
class TDDataStructures;
class BUDataStructures;
class DSNodeEquivs;
}

namespace dsa {
template<class dsa>
struct TypeSafety;
}

namespace smack {


class MemcpyCollector : public llvm::InstVisitor<MemcpyCollector> {
private:
  llvm::DSNodeEquivs *nodeEqs;
  std::vector<const llvm::DSNode*> memcpys;

public:
  MemcpyCollector(llvm::DSNodeEquivs *neqs) : nodeEqs(neqs) { }
  void visitMemCpyInst(llvm::MemCpyInst& mci);
  std::vector<const llvm::DSNode*> getMemcpys() {
    return memcpys;
  }
};

class DSAWrapper : public llvm::ModulePass {
private:
  llvm::Module *module;
  llvm::TDDataStructures *TD;
  llvm::BUDataStructures *BU;
  llvm::DSNodeEquivs *nodeEqs;
  dsa::TypeSafety<llvm::TDDataStructures> *TS;
  std::vector<const llvm::DSNode*> staticInits;
  std::vector<const llvm::DSNode*> memcpys;
  std::unordered_set<const llvm::DSNode*> intConversions;
  const llvm::DataLayout* dataLayout;

  std::vector<const llvm::DSNode*> collectMemcpys(llvm::Module &M, MemcpyCollector* mcc);
  std::vector<const llvm::DSNode*> collectStaticInits(llvm::Module &M);
  llvm::DSGraph *getGraphForValue(const llvm::Value *V);
  int getOffset(const llvm::MemoryLocation* l);

public:
  static char ID;
  DSAWrapper() : ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual bool runOnModule(llvm::Module &M);

  bool isMemcpyd(const llvm::DSNode* n);
  bool isStaticInitd(const llvm::DSNode* n);
  bool isFieldDisjoint(const llvm::Value* V, const llvm::Function* F);
  bool isFieldDisjoint(const llvm::GlobalValue* V, unsigned offset);
  bool isRead(const llvm::Value* V);
  bool isAlloced(const llvm::Value* v);
  bool isExternal(const llvm::Value* v);
  bool isSingletonGlobal(const llvm::Value *V);
  unsigned getPointedTypeSize(const llvm::Value* v);
  int getOffset(const llvm::Value* v);
  const llvm::DSNode *getNode(const llvm::Value* v);
  void printDSAGraphs(const char* Filename);
};
}

#endif // DSAWRAPPER_H
