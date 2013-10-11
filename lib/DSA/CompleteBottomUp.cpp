//===- CompleteBottomUp.cpp - Complete Bottom-Up Data Structure Graphs ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is the exact same as the bottom-up graphs, but we use take a completed
// call graph and inline all indirect callees into their callers graphs, making
// the result more useful for things like pool allocation.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "dsa-cbu"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FormattedStream.h"
using namespace llvm;

namespace {
  RegisterPass<CompleteBUDataStructures>
  X("dsa-cbu", "'Complete' Bottom-up Data Structure Analysis");
}

char CompleteBUDataStructures::ID;

//
// Method: runOnModule()
//
// Description:
//  Entry point for this pass.  Calculate the bottom up data structure graphs
//  for each function in the program.
//
// Return value:
//  true  - The module was modified.
//  false - The module was not modified.
//
bool
CompleteBUDataStructures::runOnModule (Module &M) {
  init(&getAnalysis<BUDataStructures>(), true, true, false, true);


  //
  // Make sure we have a DSGraph for all declared functions in the Module.
  // formGlobalECs assumes that DSInfo is populated with a list of
  // DSgraphs for all the functions.

  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    if (!(F->isDeclaration())){
      getOrCreateGraph(F);
    }
  }

  buildIndirectFunctionSets();
  formGlobalECs();
  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    if (!(F->isDeclaration())) {
      if (DSGraph * Graph = getOrCreateGraph(F)) {
        cloneIntoGlobals(Graph, DSGraph::DontCloneCallNodes |
                        DSGraph::DontCloneAuxCallNodes |
                        DSGraph::StripAllocaBit);
      }
    }
  }

  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    if (!(F->isDeclaration())) {
      if (DSGraph * Graph = getOrCreateGraph(F)) {
        cloneGlobalsInto(Graph, DSGraph::DontCloneCallNodes |
                        DSGraph::DontCloneAuxCallNodes);
      }
    }
  }

  //
  // Do bottom-up propagation.
  //
  bool modified = runOnModuleInternal(M);
  
  callgraph.buildSCCs();
  callgraph.buildRoots();
  
  return modified;
}

//
// Method: buildIndirectFunctionSets()
//
// Description:
//  For every indirect call site, ensure that every function target is
//  associated with a single DSNode.
//
void
CompleteBUDataStructures::buildIndirectFunctionSets (void) {
  //
  // Loop over all of the indirect calls in the program.  If a call site can
  // call multiple different functions, we need to unify all of the callees into
  // the same equivalence class.
  //
  DSGraph* G = getGlobalsGraph();
  DSGraph::ScalarMapTy& SM = G->getScalarMap();

  // Merge nodes in the global graph for these functions
  for (DSCallGraph::callee_key_iterator ii = callgraph.key_begin(),
       ee = callgraph.key_end(); ii != ee; ++ii) {

#ifndef NDEBUG
    // --Verify that for every callee of an indirect function call
    //   we have an entry in the GlobalsGraph

    // If any function in an SCC is a callee of an indirect function
    // call, the DScallgraph contains the leader of the SCC as the
    // callee of the indirect call.
    // The leasder of the SCC may not have an entry in the Globals
    // Graph, but at least one of the functions in the SCC
    // should have an entry in the GlobalsGraph

    Value *CalledValue = (*ii).getCalledValue()->stripPointerCasts();
    
    bool isIndirect = (!isa<Function>(CalledValue));
    if (isIndirect) {
      DSCallGraph::callee_iterator csii = callgraph.callee_begin(*ii),
                                   csee = callgraph.callee_end(*ii);

      for (; csii != csee; ++csii) {
        //
        // Declarations don't have to have entries.  Functions may be
        // equivalence classed already, so we have to check their equivalence
        // class leader instead of the global itself.
        //
        const Function * F = *csii;
        if (!(F->isDeclaration())){
          DSCallGraph::scc_iterator sccii = callgraph.scc_begin(F),
                                    sccee = callgraph.scc_end(F);
          bool flag = false;
          for(; sccii != sccee; ++sccii) {
            flag |= SM.count(SM.getLeaderForGlobal(*sccii));
          } 
          assert (flag &&
                  "Indirect function callee not in globals?");
         }
      }
    }
#endif

    //
    // Note: The code above and below is dealing with the fact that the targets
    // of *direct* function calls do not show up in the Scalar Map of the
    // globals graph.  The above assertion simply verifies that all targets of
    // indirect function calls show up in the Scalar Map of the globals graph,
    // and then the code below can just check the scalar map to see if the
    // call needs to be processed because it is an indirect function call.
    //
    // I suspect that this code is designed this way more for historical
    // reasons than for simplicity.  We should simplify the code is possible at
    // a future date.
    //
    // FIXME: Given the above is a valid assertion, we could probably replace
    // this code with something that *assumes* we have entries in the Scalar
    // Map.  However, because
    // I'm not convinced that we can just *skip* direct calls in this function
    // this code is careful to handle callees not existing in the globals graph
    // In other words what we have here should be correct, but might be overkill
    // that we can trim down later as needed.
    
    DSNodeHandle calleesNH;
   
    // When we build SCCs we remove any calls that are to functions in the 
    // same SCC. Hence, for every indirect call site we must assume that it
    // might call functions in its function's SCC that are address taken.
    const Function *F1 = (*ii).getInstruction()->getParent()->getParent();
    F1 = callgraph.sccLeader(&*F1);

    DSCallGraph::scc_iterator sccii = callgraph.scc_begin(F1),
                                sccee = callgraph.scc_end(F1);
    for(;sccii != sccee; ++sccii) {
      DSGraph::ScalarMapTy::const_iterator I = SM.find(SM.getLeaderForGlobal(*sccii));
      if (I != SM.end()) {
        calleesNH.mergeWith(I->second);
      }
    }

    DSCallGraph::callee_iterator csi = callgraph.callee_begin(*ii),
            cse = callgraph.callee_end(*ii);


    // We get all the callees, and then for all functions in that SCC, find the
    // ones that have entries in the GlobalsGraph.

    // We merge all the functions in the SCC that have entries, and then move
    // on to the next callee and repeat.

    // If an SCC has functions that have entries in the GlobalsGraph, and are
    // targets of an indirect function call site, they will be merged.

    // However, if an SCC has functions, that have entries in the GlobalsGraph,
    // bur are not the targets of an indirect function call site, they will not
    // be merged by CBU.

    // This NH starts off empty, but ends up merging them all together

    while(csi != cse) {
      const Function *F = *csi;
      DSCallGraph::scc_iterator sccii = callgraph.scc_begin(F),
                                sccee = callgraph.scc_end(F);
      for(;sccii != sccee; ++sccii) {
        DSGraph::ScalarMapTy::const_iterator I = SM.find(SM.getLeaderForGlobal(*sccii));
        if (I != SM.end()) {
          calleesNH.mergeWith(I->second);
        }
      }
      ++csi;
    }
  }
}
