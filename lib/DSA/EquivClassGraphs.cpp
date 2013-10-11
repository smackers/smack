//===- EquivClassGraphs.cpp - Merge equiv-class graphs & inline bottom-up -===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass is the same as the complete bottom-up graphs, but
// with functions partitioned into equivalence classes and a single merged
// DS graph for all functions in an equivalence class.  After this merging,
// graphs are inlined bottom-up on the SCCs of the final (CBU) call graph.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "ECGraphs"
#include "dsa/DataStructure.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "dsa/DSGraph.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/FormattedStream.h"
#include <fstream>
using namespace llvm;

namespace {
  RegisterPass<EquivBUDataStructures> X("dsa-eq",
                    "Equivalence-class Bottom-up Data Structure Analysis");
}
char EquivBUDataStructures::ID = 0;

// runOnModule - Calculate the bottom up data structure graphs for each function
// in the program.
//
bool EquivBUDataStructures::runOnModule(Module &M) {
  init(&getAnalysis<CompleteBUDataStructures>(), true, true, false, true);

  //make a list of all the DSGraphs
  std::set<DSGraph *>graphList;
  for(Module::iterator F = M.begin(); F != M.end(); ++F) 
  {
    if(!(F->isDeclaration()))
      graphList.insert(getOrCreateGraph(F));
  }

  //update the EQ class from indirect calls
  buildIndirectFunctionSets();
  formGlobalECs();
  mergeGraphsByGlobalECs();
  
  //remove all the DSGraph, that still have references
  for(Module::iterator F = M.begin(); F != M.end(); ++F) 
  {
    if(!(F->isDeclaration()))
      graphList.erase(getOrCreateGraph(F));
  }
  // free memory for the DSGraphs, no longer in use.
  for(std::set<DSGraph*>::iterator i = graphList.begin(),e = graphList.end();
      i!=e;i++) {
    delete (*i);
  }
  DEBUG(verifyMerging());

  formGlobalECs();

  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    if (!(F->isDeclaration())) {
      if (DSGraph * Graph = getOrCreateGraph(F)) {
        cloneGlobalsInto(Graph, DSGraph::DontCloneCallNodes |
                        DSGraph::DontCloneAuxCallNodes);
      }
    }
  }
  
  bool result = runOnModuleInternal(M); 
  
  // CBU contains the correct call graph.
  // Restore it, so that subsequent passes and clients can get it.
  restoreCorrectCallGraph();
  return result;
}

// Verifies that all the functions in an equivalence calss have been merged. 
// This is required by to be true by poolallocation.
void
EquivBUDataStructures::verifyMerging() {
  
  EquivalenceClasses<const GlobalValue*>::iterator EQSI = GlobalECs.begin();
  EquivalenceClasses<const GlobalValue*>::iterator EQSE = GlobalECs.end();
  for (;EQSI != EQSE; ++EQSI) {
    if (!EQSI->isLeader()) continue;
    EquivalenceClasses<const GlobalValue*>::member_iterator MI;
    bool first = true;
    DSGraph *firstG = 0;
    for (MI = GlobalECs.member_begin(EQSI); MI != GlobalECs.member_end(); ++MI){
      if (const Function* F = dyn_cast<Function>(*MI)){
        if (F->isDeclaration())
          continue;
          
          if(first) {
            firstG = getOrCreateGraph(F);
            first = false;
          } 
          DSGraph *G = getOrCreateGraph(F);
          if( G != firstG) {
            assert(G == firstG && "all functions in a Global EC do not have a merged graph"); 
          }
      }
    }
  }
}

//
// Method: mergeGraphsByGlobalECs()
//
// Description:
//  Merge all graphs that are in the same equivalence class.  This ensures
//  that transforms like Automatic Pool Allocation only see one graph for a 
//  call site.
//
//  After this method is executed, all functions in an equivalence class will
//  have the *same* DSGraph.
//
void
EquivBUDataStructures::mergeGraphsByGlobalECs() {
  //
  // Merge the graphs for each equivalence class.  We first scan all elements
  // in the equivalence classes and look for those elements which are leaders.
  // For each leader, we scan through all of its members and merge the DSGraphs
  // for members which are functions.
  //
 
  EquivalenceClasses<const GlobalValue*>::iterator EQSI = GlobalECs.begin();
  EquivalenceClasses<const GlobalValue*>::iterator EQSE = GlobalECs.end();
  for (;EQSI != EQSE; ++EQSI) {
    //
    // If this element is not a leader, then skip it.
    //
    if (!EQSI->isLeader()) continue;
    DSGraph* BaseGraph = 0;
    std::vector<DSNodeHandle> Args;

    //
    // Iterate through all members of this equivalence class, looking for
    // functions.
    //
    EquivalenceClasses<const GlobalValue*>::member_iterator MI;
    for (MI = GlobalECs.member_begin(EQSI); MI != GlobalECs.member_end(); ++MI){
      if (const Function* F = dyn_cast<Function>(*MI)) {
        //
        // If the function has no body, then it has no DSGraph.
        //
        // FIXME: I don't believe this is correct; the stdlib pass can assign
        //        DSGraphs to C standard library functions.
        //
        if (F->isDeclaration())
          continue;

        //
        // We have one of three possibilities:
        //  1) This is the first function we've seen.  If so, grab its DSGraph
        //     and the DSNodes for its arguments.
        //
        //  2) We have already seen this function before.  Do nothing.
        //
        //  3) We haven't seen this function before, and it's not the first one
        //     we've seen.  Merge its DSGraph into the DSGraph we're creating.
        //
        if (!BaseGraph) {
          BaseGraph = getOrCreateGraph(F);
          BaseGraph->getFunctionArgumentsForCall(F, Args);
        } else if (BaseGraph->containsFunction(F)) {
          //
          // The DSGraph for this function has already been merged into the
          // graph that we are creating.  However, that does not mean that
          // function arguments of this function have been merged with the
          // function arguments of the other functions in the equivalence graph
          // (or even with functions belonging to the same SCC in the call
          // graph).  Furthermore, it doesn't necessarily imply that the
          // contained function's DSGraph is the same as the one we're
          // building; it is possible (I think) for only the function's DSNodes
          // and other information to have been merged in.
          //
          // For these reasons, we will merge the function argument DSNodes and
          // set this function's DSGraph to be the same graph used for all
          // other function's in this equivalence class.
          //

          //
          // Merge the arguments together.
          //
          std::vector<DSNodeHandle> NextArgs;
          BaseGraph->getFunctionArgumentsForCall(F, NextArgs);
          unsigned i = 0, e = Args.size();
          for (; i != e; ++i) {
            if (i == NextArgs.size()) break;
            Args[i].mergeWith(NextArgs[i]);
          }
          for (e = NextArgs.size(); i != e; ++i)
            Args.push_back(NextArgs[i]);

          //
          // Make this function use the DSGraph that we're creating for all of
          // the functions in this equivalence class.
          //
          setDSGraph(*F, BaseGraph);
        } else {
          //
          // Merge in the DSGraph.
          //
          BaseGraph->cloneInto(getOrCreateGraph(F));

          //
          // Merge the arguments together.
          //
          std::vector<DSNodeHandle> NextArgs;
          BaseGraph->getFunctionArgumentsForCall(F, NextArgs);
          unsigned i = 0, e = Args.size();
          for (; i != e; ++i) {
            if (i == NextArgs.size()) break;
            Args[i].mergeWith(NextArgs[i]);
          }
          for (e = NextArgs.size(); i != e; ++i)
            Args.push_back(NextArgs[i]);

          //
          // Make this function use the DSGraph that we're creating for all of
          // the functions in this equivalence class.
          //
          setDSGraph(*F, BaseGraph);
        }
      }
    }

    //
    // Update the globals graph with any information that has changed due to
    // graph merging.
    //
    if (BaseGraph)
      cloneIntoGlobals(BaseGraph, DSGraph::DontCloneCallNodes |
                        DSGraph::DontCloneAuxCallNodes |
                        DSGraph::StripAllocaBit);
  }
}

