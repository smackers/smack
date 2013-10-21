//===- DSNodeEquivs.h - Build DSNode equivalence classes ------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass computes equivalence classes of DSNodes across DSGraphs.
//
//===----------------------------------------------------------------------===//

#ifndef DSNODEEQUIVS_H
#define DSNODEEQUIVS_H

#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "dsa/DSNode.h"

#include "llvm/ADT/EquivalenceClasses.h"

#include <vector>

namespace llvm {

typedef std::vector<const Function *> FunctionList;
typedef FunctionList::iterator FunctionList_it;

class DSNodeEquivs : public ModulePass {
private:
  EquivalenceClasses<const DSNode*> Classes;

  void buildDSNodeEquivs(Module &M);

  void addNodesFromGraph(DSGraph *G);
  FunctionList getCallees(CallSite &CS);
  void equivNodesThroughCallsite(CallInst *CI);
  void equivNodesToGlobals(DSGraph *G);
  void equivNodeMapping(DSGraph::NodeMapTy & NM);
  
public:
  static char ID;

  DSNodeEquivs() : ModulePass(ID) {}

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequiredTransitive<TDDataStructures>();
    AU.setPreservesAll();
  }

  bool runOnModule(Module &M);

  // Returns the computed equivalence classes.  Two DSNodes in the same
  // equivalence class may alias.  DSNodes may also alias if they have the
  // Incomplete, Unknown, or External flags set (even if they are in different
  // equivalence classes).
  const EquivalenceClasses<const DSNode*> &getEquivalenceClasses();

  // Returns a DSNode for the specified value.  Note that two nodes may alias
  // even if they have different DSNodes (because the DSNodes may belong to
  // different DSGraphs).
  const DSNode *getMemberForValue(const Value *V);
};

}

#endif // DSNODEEQUIVS_H
