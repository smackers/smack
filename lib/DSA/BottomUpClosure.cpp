//===- BottomUpClosure.cpp - Compute bottom-up interprocedural closure ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the BUDataStructures class, which represents the
// Bottom-Up Interprocedural closure of the data structure graph over the
// program.  This is useful for applications like pool allocation, but **not**
// applications like alias analysis.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "dsa-bu"
#include "llvm/IR/Constants.h"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FormattedStream.h"

using namespace llvm;

namespace {
  STATISTIC (MaxSCC, "Maximum SCC Size in Call Graph");
  STATISTIC (NumInlines, "Number of graphs inlined");
  STATISTIC (NumCallEdges, "Number of 'actual' call edges");
  STATISTIC (NumIndResolved, "Number of resolved IndCalls");
  STATISTIC (NumIndUnresolved, "Number of unresolved IndCalls");
  // NumEmptyCalls = NumIndUnresolved + Number of calls to external functions
  STATISTIC (NumEmptyCalls, "Number of calls we know nothing about");
  STATISTIC (NumRecalculations, "Number of DSGraph recalculations");
  STATISTIC (NumRecalculationsSkipped, "Number of DSGraph recalculations skipped");

  RegisterPass<BUDataStructures>
  X("dsa-bu", "Bottom-up Data Structure Analysis");
}

char BUDataStructures::ID;

// run - Calculate the bottom up data structure graphs for each function in the
// program.
//
bool BUDataStructures::runOnModule(Module &M) {
  init(&getAnalysis<StdLibDataStructures>(), true, true, false, false );

  return runOnModuleInternal(M);
}

// BU:
// Construct the callgraph from the local graphs
// Find SCCs
// inline bottom up
//
bool BUDataStructures::runOnModuleInternal(Module& M) {

  //
  // Make sure we have a DSGraph for all declared functions in the Module.
  // While we may not need them in this DSA pass, a later DSA pass may ask us
  // for their DSGraphs, and we want to have them if asked.
  //
  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    if (!(F->isDeclaration())){
      getOrCreateGraph(F);
    }
  }

  //
  // Do a post-order traversal of the SCC callgraph and do bottom-up inlining.
  //
  postOrderInline (M);

  // At the end of the bottom-up pass, the globals graph becomes complete.
  // FIXME: This is not the right way to do this, but it is sorta better than
  // nothing!  In particular, externally visible globals and unresolvable call
  // nodes at the end of the BU phase should make things that they point to
  // incomplete in the globals graph.
  //

  GlobalsGraph->removeTriviallyDeadNodes();
  GlobalsGraph->maskIncompleteMarkers();

  // Mark external globals incomplete.
  GlobalsGraph->markIncompleteNodes(DSGraph::IgnoreGlobals);
  GlobalsGraph->computeExternalFlags(DSGraph::DontMarkFormalsExternal);
  GlobalsGraph->computeIntPtrFlags();

  //
  // Create equivalence classes for aliasing globals so that we only need to
  // record one global per DSNode.
  //
  formGlobalECs();

  // Merge the globals variables (not the calls) from the globals graph back
  // into the individual function's graph so that changes made to globals during
  // BU can be reflected. This is specifically needed for correct call graph
  //
  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    if (!(F->isDeclaration())){
      DSGraph *Graph  = getOrCreateGraph(F);
      cloneGlobalsInto(Graph, DSGraph::DontCloneCallNodes |
                        DSGraph::DontCloneAuxCallNodes);
      Graph->buildCallGraph(callgraph, GlobalFunctionList, filterCallees);
      Graph->maskIncompleteMarkers();
      Graph->markIncompleteNodes(DSGraph::MarkFormalArgs |
                                   DSGraph::IgnoreGlobals);
      Graph->computeExternalFlags(DSGraph::DontMarkFormalsExternal);
      Graph->computeIntPtrFlags();
    }
  }

  // Once the correct flags have been calculated. Update the callgraph.
  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    if (!(F->isDeclaration())){
      DSGraph *Graph = getOrCreateGraph(F);
      Graph->buildCompleteCallGraph(callgraph,
                                    GlobalFunctionList, filterCallees);
    }
  }

  NumCallEdges += callgraph.size();

  // Put the call graph in canonical form
  callgraph.buildSCCs();
  callgraph.buildRoots();

  return false;
}

//
// Function: applyCallsiteFilter
//
// Description:
//  Given a DSCallSite, and a list of functions, filter out the ones
//  that aren't callable from the given Callsite.
//
//  Does no filtering if 'filterCallees' is set to false.
//
void BUDataStructures::
applyCallsiteFilter(const DSCallSite &DCS, FuncSet &Callees) {

  if (!filterCallees) return;

  FuncSet::iterator I = Callees.begin();
  CallSite CS = DCS.getCallSite();
  while (I != Callees.end()) {
    if (functionIsCallable(CS, *I)) {
      ++I;
    } else {
      I = Callees.erase(I);
    }
  }
}

//
// Function: getAllCallees()
//
// Description:
//  Given a DSCallSite, add to the list the functions that can be called by
//  the call site *if* it is resolvable.  Uses 'applyCallsiteFilter' to
//  only add the functions that are valid targets of this callsite.
//
void BUDataStructures::
getAllCallees(const DSCallSite &CS, FuncSet &Callees) {
  //
  // FIXME: Should we check for the Unknown flag on indirect call sites?
  //
  // Direct calls to functions that have bodies are always resolvable.
  // Indirect function calls that are for a complete call site (the analysis
  // knows everything about the call site) and do not target external functions
  // are also resolvable.
  //
  if (CS.isDirectCall()) {
    if (!CS.getCalleeFunc()->isDeclaration())
      Callees.insert(CS.getCalleeFunc());
  } else if (CS.getCalleeNode()->isCompleteNode()) {
    // Get all callees.
    if (!CS.getCalleeNode()->isExternFuncNode()) {
      // Get all the callees for this callsite
      FuncSet TempCallees;
      CS.getCalleeNode()->addFullFunctionSet(TempCallees);
      // Filter out the ones that are invalid targets with respect
      // to this particular callsite.
      applyCallsiteFilter(CS, TempCallees);
      // Insert the remaining callees (legal ones, if we're filtering)
      // into the master 'Callees' list
      Callees.insert(TempCallees.begin(), TempCallees.end());
    }
  }
}

//
// Function: getAllAuxCallees()
//
// Description:
//  Return a list containing all of the resolvable callees in the auxiliary
//  list for the specified graph in the Callees vector.
//
// Inputs:
//  G - The DSGraph for which the callers wants a list of resolvable call
//      sites.
//
// Outputs:
//  Callees - A list of all functions that can be called from resolvable call
//            sites.  This list is always cleared by this function before any
//            functions are added to it.
//
void BUDataStructures::
getAllAuxCallees (DSGraph* G, FuncSet & Callees) {
  //
  // Clear out the list of callees.
  //
  Callees.clear();
  for (DSGraph::afc_iterator I = G->afc_begin(), E = G->afc_end(); I != E; ++I)
    getAllCallees(*I, Callees);
}

//
// Method: postOrderInline()
//
// Description:
//  This methods does a post order traversal of the call graph and performs
//  bottom-up inlining of the DSGraphs.
//
void
BUDataStructures::postOrderInline (Module & M) {
  // Variables used for Tarjan SCC-finding algorithm.  These are passed into
  // the recursive function used to find SCCs.
  std::vector<const Function*> Stack;
  std::map<const Function*, unsigned> ValMap;
  unsigned NextID = 1;


  // Do post order traversal on the global ctors. Use this information to update
  // the globals graph.
  const char *Name = "llvm.global_ctors";
  GlobalVariable *GV = M.getNamedGlobal(Name);
  if (GV && !(GV->isDeclaration()) && !(GV->hasLocalLinkage())) {
    // Should be an array of '{ int, void ()* }' structs.  The first value is
    // the init priority, which we ignore.
    ConstantArray *InitList = dyn_cast<ConstantArray>(GV->getInitializer());
    if (InitList) {
      for (unsigned i = 0, e = InitList->getNumOperands(); i != e; ++i)
        if (ConstantStruct *CS = dyn_cast<ConstantStruct>(InitList->getOperand(i))) {
          if (CS->getNumOperands() != 2) 
            break; // Not array of 2-element structs.
          Constant *FP = CS->getOperand(1);
          if (FP->isNullValue())
            break;  // Found a null terminator, exit.
   
          if (ConstantExpr *CE = dyn_cast<ConstantExpr>(FP))
            if (CE->isCast())
              FP = CE->getOperand(0);
          Function *F = dyn_cast<Function>(FP);
          if (F && !F->isDeclaration() && !ValMap.count(F)) {
            calculateGraphs(F, Stack, NextID, ValMap);
            CloneAuxIntoGlobal(getDSGraph(*F));
          }
        }
      GlobalsGraph->removeTriviallyDeadNodes();
      GlobalsGraph->maskIncompleteMarkers();

      // Mark external globals incomplete.
      GlobalsGraph->markIncompleteNodes(DSGraph::IgnoreGlobals);
      GlobalsGraph->computeExternalFlags(DSGraph::DontMarkFormalsExternal);
      GlobalsGraph->computeIntPtrFlags();

      //
      // Create equivalence classes for aliasing globals so that we only need to
      // record one global per DSNode.
      //
      formGlobalECs();
      // propogte information calculated 
      // from the globals graph to the other graphs.
      for (Module::iterator F = M.begin(); F != M.end(); ++F) {
        if (!(F->isDeclaration())){
          DSGraph *Graph  = getDSGraph(*F);
          cloneGlobalsInto(Graph, DSGraph::DontCloneCallNodes |
                           DSGraph::DontCloneAuxCallNodes);
          Graph->buildCallGraph(callgraph, GlobalFunctionList, filterCallees);
          Graph->maskIncompleteMarkers();
          Graph->markIncompleteNodes(DSGraph::MarkFormalArgs |
                                     DSGraph::IgnoreGlobals);
          Graph->computeExternalFlags(DSGraph::DontMarkFormalsExternal);
          Graph->computeIntPtrFlags();
        }
      }
    }
  }
 
  //
  // Start the post order traversal with the main() function.  If there is no
  // main() function, don't worry; we'll have a separate traversal for inlining
  // graphs for functions not reachable from main().
  //
  Function *MainFunc = M.getFunction ("main");
  if (MainFunc && !MainFunc->isDeclaration()) {
    calculateGraphs(MainFunc, Stack, NextID, ValMap);
    CloneAuxIntoGlobal(getDSGraph(*MainFunc));
  }

  //
  // Calculate the graphs for any functions that are unreachable from main...
  //
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
    if (!I->isDeclaration() && !ValMap.count(I)) {
      if (MainFunc)
        DEBUG(errs() << debugname << ": Function unreachable from main: "
        << I->getName() << "\n");
      calculateGraphs(I, Stack, NextID, ValMap);     // Calculate all graphs.
      CloneAuxIntoGlobal(getDSGraph(*I));

      // Mark this graph as processed.  Do this by finding all functions
      // in the graph that map to it, and mark them visited.
      // Note that this really should be handled neatly by calculateGraphs
      // itself, not here.  However this catches the worst offenders.
      DSGraph *G = getDSGraph(*I);
      for(DSGraph::retnodes_iterator RI = G->retnodes_begin(),
          RE = G->retnodes_end(); RI != RE; ++RI) {
        if (getDSGraph(*RI->first) == G) {
          if (!ValMap.count(RI->first))
            ValMap[RI->first] = ~0U;
          else
            assert(ValMap[RI->first] == ~0U);
        }
      }
    }
  return;
}

static bool hasNewCallees(svset<const Function*> &New,
                          svset<const Function*> &Old) {
  if (New.size() > Old.size()) return true;

  svset<const Function*>::iterator NI = New.begin(), NE = New.end();

  for (; NI != NE; ++NI)
    if (!Old.count(*NI)) return true;

  return false;
}

//
// Method: calculateGraphs()
//
// Description:
//  Perform recursive bottom-up inlining of DSGraphs from callee to caller.
//
// Inputs:
//  F - The function which should have its callees' DSGraphs merged into its
//      own DSGraph.
//  Stack - The stack used for Tarjan's SCC-finding algorithm.
//  NextID - The nextID value used for Tarjan's SCC-finding algorithm.
//  ValMap - The map used for Tarjan's SCC-finding algorithm.
//
// Return value:
//
unsigned
BUDataStructures::calculateGraphs (const Function *F,
                                   TarjanStack & Stack,
                                   unsigned & NextID,
                                   TarjanMap & ValMap) {
  assert(!ValMap.count(F) && "Shouldn't revisit functions!");
  unsigned Min = NextID++, MyID = Min;
  ValMap[F] = Min;
  Stack.push_back(F);

  //
  // FIXME: This test should be generalized to be any function that we have
  // already processed in the case when there isn't a main() or there are
  // unreachable functions!
  //
  if (F->isDeclaration()) {   // sprintf, fprintf, sscanf, etc...
    // No callees!
    Stack.pop_back();
    ValMap[F] = ~0;
    return Min;
  }

  //
  // Get the DSGraph of the current function.  Make one if one doesn't exist.
  //
  DSGraph* Graph = getOrCreateGraph(F);

  //
  // Find all callee functions.  Use the DSGraph for this (do not use the call
  // graph (DSCallgraph) as we're still in the process of constructing it).
  //
  FuncSet CalleeFunctions;
  getAllAuxCallees(Graph, CalleeFunctions);

  //
  // Iterate through each call target (these are the edges out of the current
  // node (i.e., the current function) in Tarjan graph parlance).  Find the
  // minimum assigned ID.
  //
  for (FuncSet::iterator I = CalleeFunctions.begin(), E = CalleeFunctions.end();
       I != E; ++I) {
    const Function *Callee = *I;
    unsigned M;
    //
    // If we have not visited this callee before, visit it now (this is the
    // post-order component of the Bottom-Up algorithm).  Otherwise, look up
    // the assigned ID value from the Tarjan Value Map.
    //
    TarjanMap::iterator It = ValMap.find(Callee);
    if (It == ValMap.end())  // No, visit it now.
      M = calculateGraphs(Callee, Stack, NextID, ValMap);
    else                    // Yes, get it's number.
      M = It->second;

    //
    // If we've found a function with a smaller ID than this funtion, record
    // that ID as the minimum ID.
    //
    if (M < Min) Min = M;
  }

  assert(ValMap[F] == MyID && "SCC construction assumption wrong!");

  //
  // If the minimum ID found is not this function's ID, then this function is
  // part of a larger SCC.
  //
  if (Min != MyID)
    return Min;

  //
  // If this is a new SCC, process it now.
  //
  if (Stack.back() == F) {           // Special case the single "SCC" case here.
    DEBUG(errs() << "Visiting single node SCC #: " << MyID << " fn: "
	  << F->getName() << "\n");
    Stack.pop_back();
    DEBUG(errs() << "  [BU] Calculating graph for: " << F->getName()<< "\n");
    DSGraph* G = getOrCreateGraph(F);
    calculateGraph(G);
    DEBUG(errs() << "  [BU] Done inlining: " << F->getName() << " ["
	  << G->getGraphSize() << "+" << G->getAuxFunctionCalls().size()
	  << "]\n");

    if (MaxSCC < 1) MaxSCC = 1;

    //
    // Should we revisit the graph?  Only do it if there are now new resolvable
    // callees.
    FuncSet NewCallees;
    getAllAuxCallees(G, NewCallees);
    if (!NewCallees.empty()) {
      if (hasNewCallees(NewCallees, CalleeFunctions)) {
        DEBUG(errs() << "Recalculating " << F->getName() << " due to new knowledge\n");
        ValMap.erase(F);
        ++NumRecalculations;
        return calculateGraphs(F, Stack, NextID, ValMap);
      }
      ++NumRecalculationsSkipped;
    }
    ValMap[F] = ~0U;
    return MyID;
  } else {
    unsigned SCCSize = 1;
    const Function *NF = Stack.back();
    if(NF != F)
      ValMap[NF] = ~0U;
    DSGraph* SCCGraph = getDSGraph(*NF);

    //
    // First thing first: collapse all of the DSGraphs into a single graph for
    // the entire SCC.  Splice all of the graphs into one and discard all of
    // the old graphs.
    //
    while (NF != F) {
      Stack.pop_back();
      NF = Stack.back();
      if(NF != F)
        ValMap[NF] = ~0U;

      DSGraph* NFG = getDSGraph(*NF);

      if (NFG != SCCGraph) {
        // Update the Function -> DSG map.
        for (DSGraph::retnodes_iterator I = NFG->retnodes_begin(),
               E = NFG->retnodes_end(); I != E; ++I)
          setDSGraph(*I->first, SCCGraph);
        
        SCCGraph->spliceFrom(NFG);
        delete NFG;
        ++SCCSize;
      }
    }
    Stack.pop_back();

    DEBUG(errs() << "Calculating graph for SCC #: " << MyID << " of size: "
	  << SCCSize << "\n");

    // Compute the Max SCC Size.
    if (MaxSCC < SCCSize)
      MaxSCC = SCCSize;

    // Clean up the graph before we start inlining a bunch again...
    SCCGraph->removeDeadNodes(DSGraph::KeepUnreachableGlobals);

    // Now that we have one big happy family, resolve all of the call sites in
    // the graph...
    calculateGraph(SCCGraph);
    DEBUG(errs() << "  [BU] Done inlining SCC  [" << SCCGraph->getGraphSize()
	  << "+" << SCCGraph->getAuxFunctionCalls().size() << "]\n"
	  << "DONE with SCC #: " << MyID << "\n");
    FuncSet NewCallees;
    getAllAuxCallees(SCCGraph, NewCallees);
    if (!NewCallees.empty()) {
      if (hasNewCallees(NewCallees, CalleeFunctions)) {
        DEBUG(errs() << "Recalculating SCC Graph " << F->getName() << " due to new knowledge\n");
        ValMap.erase(F);
        ++NumRecalculations;
        return calculateGraphs(F, Stack, NextID, ValMap);
      }
      ++NumRecalculationsSkipped;
    }
    ValMap[F] = ~0U;
    return MyID;
  }
}

//
// Method: CloneAuxIntoGlobal()
//
// Description:
//  This method takes the specified graph and processes each unresolved call
//  site (a call site for which all targets are not yet known). For each
//  unresolved call site, it adds it to the globals graph and merges
//  information about the call site if the globals graph already had the call
//  site in its own list of unresolved call sites.
//
void BUDataStructures::CloneAuxIntoGlobal(DSGraph* G) {
  //
  // If this DSGraph has no unresolved call sites, do nothing.  We do enough
  // work that wastes time even when the list is empty that this extra check
  // is probably worth it.
  //
  if (G->afc_begin() == G->afc_end())
    return;

  DSGraph* GG = G->getGlobalsGraph();
  ReachabilityCloner RC(GG, G, 0);

  //
  // Determine which called values are both within the local graph DSCallsites
  // and the global graph DSCallsites.  Note that we require that the global
  // graph have a DSNode for the called value.
  //
  std::map<Value *, DSCallSite *> CommonCallValues;
  for (DSGraph::afc_iterator ii = G->afc_begin(), ee = G->afc_end();
       ii != ee;
       ++ii) {
    //
    // If the globals graph has a DSNode for the LLVM value used in the local
    // unresolved call site, then it might have a DSCallSite for it, too.
    // Record this call site as a potential call site that will need to be
    // merged.
    //
    // Otherwise, just add the call site to the globals graph.
    //
    Value * V = ii->getCallSite().getCalledValue();
    if (GG->hasNodeForValue(V)) {
      DSCallSite & DS = *ii;
      CommonCallValues[V] = &DS;
    } else {
      GG->addAuxFunctionCall(RC.cloneCallSite(*ii));
    }
  }

  //
  // Scan through all the unresolved call sites in the globals graph and see if
  // the local graph has a call using the same LLVM value.  If so, merge the
  // call sites.
  //
  DSGraph::afc_iterator GGii = GG->afc_begin();
  for (; GGii != GG->afc_end(); ++GGii) {
    //
    // Determine if this unresolved call site is also in the local graph.
    // If so, then merge it.
    //
    Value * CalledValue = GGii->getCallSite().getCalledValue();
    std::map<Value *, DSCallSite *>::iterator v;
    v = CommonCallValues.find (CalledValue);
    if (v != CommonCallValues.end()) {
      //
      // Merge the unresolved call site into the globals graph.
      //
      RC.cloneCallSite(*(v->second)).mergeWith(*GGii);

      //
      // Mark that this call site was merged by removing the called LLVM value
      // from the set of values common to both the local and global DSGraphs.
      //
      CommonCallValues.erase (v);
    }
  }

  //
  // We've now merged all DSCallSites that were known both to the local graph
  // and the globals graph.  Now, there are still some local call sites that
  // need to be *added* to the globals graph; they are in DSCallSites remaining
  // in CommonCallValues.
  //
  std::map<Value *, DSCallSite *>::iterator v = CommonCallValues.begin ();
  for (; v != CommonCallValues.end(); ++v) {
    GG->addAuxFunctionCall(RC.cloneCallSite(*(v->second)));
  }

  return;
}


//
// Description:
//  Inline all graphs in the callgraph and remove callsites that are completely
//  dealt with
//
void BUDataStructures::calculateGraph(DSGraph* Graph) {
  DEBUG(Graph->AssertGraphOK(); Graph->getGlobalsGraph()->AssertGraphOK());
  Graph->buildCallGraph(callgraph, GlobalFunctionList, filterCallees);

  // Move our call site list into TempFCs so that inline call sites go into the
  // new call site list and doesn't invalidate our iterators!
  DSGraph::FunctionListTy TempFCs;
  DSGraph::FunctionListTy &AuxCallsList = Graph->getAuxFunctionCalls();
  TempFCs.swap(AuxCallsList);

  for(DSGraph::FunctionListTy::iterator I = TempFCs.begin(), E = TempFCs.end();
      I != E; ++I) {
    DEBUG(Graph->AssertGraphOK(); Graph->getGlobalsGraph()->AssertGraphOK());

    DSCallSite &CS = *I;

    // Fast path for noop calls.  Note that we don't care about merging globals
    // in the callee with nodes in the caller here.
    if (!CS.isIndirectCall() && CS.getRetVal().isNull()
        && CS.getNumPtrArgs() == 0 && !CS.isVarArg()) {
      continue;
    }

    // If this callsite is unresolvable, get rid of it now.
    if (CS.isUnresolvable()) {
      continue;
    }

    // Find all callees for this callsite, according to the DSGraph!
    // Do *not* use the callgraph, because we're updating that as we go!
    FuncSet CalledFuncs;
    getAllCallees(CS,CalledFuncs);

    if (CalledFuncs.empty()) {
      ++NumEmptyCalls;
      if (CS.isIndirectCall())
        ++NumIndUnresolved;
      // Remember that we could not resolve this yet!
      DSGraph::FunctionListTy::iterator S = I++;
      AuxCallsList.splice(AuxCallsList.end(), TempFCs, S);
      continue;
    }
    // If we get to this point, we know the callees, and can inline.
    // This means, that either it is a direct call site. Or if it is
    // an indirect call site, its calleeNode is complete, and we can
    // resolve this particular call site.
    assert((CS.isDirectCall() || CS.getCalleeNode()->isCompleteNode())
       && "Resolving an indirect incomplete call site");

    if (CS.isIndirectCall()) {
        ++NumIndResolved;
    }

    DSGraph *GI;

    for (FuncSet::iterator I = CalledFuncs.begin(), E = CalledFuncs.end();
         I != E; ++I) {
      const Function *Callee = *I;
      // Get the data structure graph for the called function.

      GI = getDSGraph(*Callee);  // Graph to inline
      DEBUG(GI->AssertGraphOK(); GI->getGlobalsGraph()->AssertGraphOK());
      DEBUG(errs() << "    Inlining graph for " << Callee->getName()
	    << "[" << GI->getGraphSize() << "+"
	    << GI->getAuxFunctionCalls().size() << "] into '"
	    << Graph->getFunctionNames() << "' [" << Graph->getGraphSize() <<"+"
	    << Graph->getAuxFunctionCalls().size() << "]\n");

      //
      // Merge in the DSGraph of the called function.
      //
      // TODO:
      //  Why are the strip alloca bit and don't clone call nodes bit set?
      //
      //  I believe the answer is on page 6 of the PLDI paper on DSA.  The
      //  idea is that stack objects are invalid if they escape.
      //
      Graph->mergeInGraph(CS, *Callee, *GI,
                          DSGraph::StripAllocaBit|DSGraph::DontCloneCallNodes);
      ++NumInlines;
      DEBUG(Graph->AssertGraphOK(););
    }
  }
  TempFCs.clear();

  // Recompute the Incomplete markers
  Graph->maskIncompleteMarkers();
  Graph->markIncompleteNodes(DSGraph::MarkFormalArgs);
  Graph->computeExternalFlags(DSGraph::DontMarkFormalsExternal);
  Graph->computeIntPtrFlags();

  //
  // Update the callgraph with the new information that we have gleaned.
  // NOTE : This must be called before removeDeadNodes, so that no 
  // information is lost due to deletion of DSCallNodes.
  Graph->buildCallGraph(callgraph, GlobalFunctionList, filterCallees);

  // Delete dead nodes.  Treat globals that are unreachable but that can
  // reach live nodes as live.
  Graph->removeDeadNodes(DSGraph::KeepUnreachableGlobals);

  cloneIntoGlobals(Graph, DSGraph::DontCloneCallNodes |
                        DSGraph::DontCloneAuxCallNodes |
                        DSGraph::StripAllocaBit);
  //Graph->writeGraphToFile(cerr, "bu_" + F.getName());
}

