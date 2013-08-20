//===- DataStructureCallGraph.h - Provide a CallGraph using DSA -----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file declares the DataStructureCallGraph implementation of the
// CallGraph analysis. Based on llvm/lib/Analysis/IPA/CallGraph.cpp.
//
//===----------------------------------------------------------------------===//

#ifndef _DATA_STRUCTURE_CALLGRAPH_H
#define _DATA_STRUCTURE_CALLGRAPH_H

#include "dsa/CallTargets.h"
#include "dsa/DataStructure.h"

#include "llvm/Module.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

namespace llvm {

class DataStructureCallGraph : public ModulePass, public CallGraph {
  // Root is root of the call graph, or the external node if a 'main' function
  // couldn't be found.
  CallGraphNode *Root;

  // ExternalCallingNode - This node has edges to all external functions and
  // those internal functions that have their address taken.
  CallGraphNode *ExternalCallingNode;

  // CallsExternalNode - This node has edges to it from all functions making
  // indirect calls or calling an external function.
  CallGraphNode *CallsExternalNode;

  typedef dsa::CallTargetFinder<TDDataStructures> CallTargetFinderTy;

public:
  static char ID;
  DataStructureCallGraph() :
    ModulePass(ID), Root(0), ExternalCallingNode(0), CallsExternalNode(0) { }

  virtual bool runOnModule(Module &M);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<TDDataStructures>();
    AU.addRequired<CallTargetFinderTy>();
    AU.setPreservesAll();
  }

  virtual void print(raw_ostream &OS, const Module *) const {
    OS << "CallGraph Root is: ";
    if (Function *F = getRoot()->getFunction())
      OS << F->getName() << "\n";
    else {
      OS << "<<null function: 0x" << getRoot() << ">>\n";
    }
    
    CallGraph::print(OS, 0);
  }

  virtual void releaseMemory() {
    destroy();
  }
  
  // getAdjustedAnalysisPointer - This method is used when a pass implements an
  // analysis interface through multiple inheritance. If needed, it should
  // override this to adjust the this pointer as needed for the specified pass
  // info.
  virtual void *getAdjustedAnalysisPointer(AnalysisID PI) {
    if (PI == &CallGraph::ID)
      return (CallGraph*)this;
    return this;
  }
  
  CallGraphNode* getExternalCallingNode() const { return ExternalCallingNode; }
  CallGraphNode* getCallsExternalNode()   const { return CallsExternalNode; }

  // getRoot - Return the root of the call graph, which is either main, or if
  // main cannot be found, the external node.
  CallGraphNode *getRoot()             { return Root; }
  const CallGraphNode *getRoot() const { return Root; }

private:
  // addToCallGraph - Add a function to the call graph, and link the node to all
  // of the functions that it calls.
  void addToCallGraph(Function *F);

  // destroy - Release memory for the call graph
  virtual void destroy() {
    // CallsExternalNode is not in the function map, delete it explicitly.
    if (CallsExternalNode) {
      CallsExternalNode->allReferencesDropped();
      delete CallsExternalNode;
      CallsExternalNode = 0;
    }
    CallGraph::destroy();
  }
};

}

#endif // _DATA_STRUCTURE_CALLGRAPH_H
