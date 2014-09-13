//===- DataStructureCallGraph.cpp - Provide a CallGraph using DSA ---------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file contains the DataStructureCallGraph implementation of the
// CallGraph analysis. Based on llvm/lib/Analysis/IPA/CallGraph.cpp.
//
//===----------------------------------------------------------------------===//

#include "assistDS/DataStructureCallGraph.h"
#include "dsa/DSGraph.h"
#include "dsa/DSNode.h"

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"

using namespace llvm;

char DataStructureCallGraph::ID;

namespace {

static RegisterPass<DataStructureCallGraph>
X("dsa-cg", "DSA-based CallGraph implementation");

RegisterAnalysisGroup<CallGraphWrapperPass> Y(X); 

}

bool DataStructureCallGraph::runOnModule(Module &M) {
  ExternalCallingNode = getOrInsertFunction(0);
  CallsExternalNode = new CallGraphNode(0);
  Root = 0;

  // Add every function to the call graph.
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
    addToCallGraph(I);

  // If we didn't find a main function, use the external call graph node
  if (Root == 0) Root = ExternalCallingNode;
  
  return false;
}

// Add a function to the call graph, and link the node to all of the functions
// that it calls.
void DataStructureCallGraph::addToCallGraph(Function *F) {
  CallGraphNode *Node = getOrInsertFunction(F);

  if (!F->hasLocalLinkage()) {
    ExternalCallingNode->addCalledFunction(CallSite(), Node);

    // Found the entry point?
    if (F->getName() == "main") {
      if (Root)    // Found multiple external mains?  Don't pick one.
        Root = ExternalCallingNode;
      else
        Root = Node; // Found a main, keep track of it!
    }
  }

  // If this function is not defined in this translation unit, it could call
  // anything.
  if (F->isDeclaration() && !F->isIntrinsic()) {
    Node->addCalledFunction(CallSite(), CallsExternalNode);
    return;
  }

  TDDataStructures &DS = getAnalysis<TDDataStructures>();
  DSGraph &GG = *DS.getGlobalsGraph();
  CallTargetFinderTy &CTF = getAnalysis<CallTargetFinderTy>();

  // Determine if the function can be called by external code by looking up
  // its DSNode in the globals graph. A node marked External, Unknown, or
  // Incomplete has the possibility of being called from external code.
  DSNode *N = GG.getNodeForValue(F).getNode();

  if (N &&
      (N->isExternalNode() ||
       N->isUnknownNode() ||
       N->isIncompleteNode())) {
    ExternalCallingNode->addCalledFunction(CallSite(), Node);
  }

  // Go over the instructions in the function and determine the call targets
  // for each call site.
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    CallSite CS(&*I);

    // Only look through valid call sites that are not calls to intrinsics.
    if (!CS || isa<IntrinsicInst>(&*I))
      continue;

    if (const Function *F = 
        dyn_cast<Function>(CS.getCalledValue()->stripPointerCasts())) {
      // Direct call: Don't use DSA, just add the function we discovered as
      // the call target.

      Node->addCalledFunction(CS, getOrInsertFunction(F));
    } else {
      // Indirect call: Use CallTargetFinder to determine the set of targets to
      // the indirect call site. Be conservative about incomplete call sites.

      if (!CTF.isComplete(CS)) {
        // Add CallsExternalNode as a target of incomplete call sites.
        Node->addCalledFunction(CS, CallsExternalNode);
      }

      SmallPtrSet<const Function *, 16> Targets(CTF.begin(CS), CTF.end(CS));

      for (SmallPtrSet<const Function *, 16>::const_iterator
           TI = Targets.begin(), TE = Targets.end(); TI != TE; ++TI) {
        Node->addCalledFunction(CS, getOrInsertFunction(*TI));
      }
    }
  }
}
