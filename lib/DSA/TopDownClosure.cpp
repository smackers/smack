//===- TopDownClosure.cpp - Compute the top-down interprocedure closure ---===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the TDDataStructures class, which represents the
// Top-down Interprocedural closure of the data structure graph over the
// program.  This is useful (but not strictly necessary?) for applications
// like pointer analysis.
//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "td_dsa"

#include "dsa/DataStructure.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DerivedTypes.h"
#include "dsa/DSGraph.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Timer.h"
#include "llvm/ADT/Statistic.h"
using namespace llvm;

#define TIME_REGION(VARNAME, DESC)

namespace {
  RegisterPass<TDDataStructures>   // Register the pass
  Y("dsa-td", "Top-down Data Structure Analysis");

  RegisterPass<EQTDDataStructures>   // Register the pass
  Z("dsa-eqtd", "EQ Top-down Data Structure Analysis");

  STATISTIC (NumTDInlines, "Number of graphs inlined");
}

char TDDataStructures::ID;
char EQTDDataStructures::ID;

TDDataStructures::~TDDataStructures() {
  releaseMemory();
}

EQTDDataStructures::~EQTDDataStructures() {
  releaseMemory();
}

void TDDataStructures::markReachableFunctionsExternallyAccessible(DSNode *N,
                                                   DenseSet<DSNode*> &Visited) {
  if (!N || Visited.count(N)) return;
  Visited.insert(N);

  // Handle this node
  {
    N->addFullFunctionSet(ExternallyCallable);
  }

  for (DSNode::edge_iterator ii = N->edge_begin(),
          ee = N->edge_end(); ii != ee; ++ii)
    if (!ii->second.isNull()) {
      DSNodeHandle &NH = ii->second;
      DSNode * NN = NH.getNode();
      NN->addFullFunctionSet(ExternallyCallable);
      markReachableFunctionsExternallyAccessible(NN, Visited);
    }
}


// run - Calculate the top down data structure graphs for each function in the
// program.
//
bool TDDataStructures::runOnModule(Module &M) {

  init(useEQBU ? &getAnalysis<EquivBUDataStructures>()
       : &getAnalysis<BUDataStructures>(),
       true, true, true, false);
  // Figure out which functions must not mark their arguments complete because
  // they are accessible outside this compilation unit.  Currently, these
  // arguments are functions which are reachable by incomplete or external
  // nodes in the globals graph.
  const DSScalarMap &GGSM = GlobalsGraph->getScalarMap();
  DenseSet<DSNode*> Visited;
  for (DSScalarMap::global_iterator I=GGSM.global_begin(), E=GGSM.global_end();
       I != E; ++I) {
    DSNode *N = GGSM.find(*I)->second.getNode();
    if (N->isIncompleteNode() || N->isExternalNode())
      markReachableFunctionsExternallyAccessible(N, Visited);
  }

  // Loop over unresolved call nodes.  Any functions passed into (but not
  // returned!) from unresolvable call nodes may be invoked outside of the
  // current module.
  for (DSGraph::afc_iterator I = GlobalsGraph->afc_begin(),
         E = GlobalsGraph->afc_end(); I != E; ++I)
    for (unsigned arg = 0, e = I->getNumPtrArgs(); arg != e; ++arg)
      markReachableFunctionsExternallyAccessible(I->getPtrArg(arg).getNode(),
                                                 Visited);
  Visited.clear();

  // Clear Aux of Globals Graph to be refilled in later by post-TD unresolved
  // functions
  GlobalsGraph->getAuxFunctionCalls().clear();

  // Functions without internal linkage are definitely externally callable!
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
    if (!I->isDeclaration() && !I->hasInternalLinkage() && !I->hasPrivateLinkage())
      ExternallyCallable.insert(I);

  // Debug code to print the functions that are externally callable
#if 0
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
    if (ExternallyCallable.count(I)) {
      errs() << "ExternallyCallable: " << I->getNameStr() << "\n";
    }
#endif

  // We want to traverse the call graph in reverse post-order.  To do this, we
  // calculate a post-order traversal, then reverse it.
  DenseSet<DSGraph*> VisitedGraph;
  std::vector<DSGraph*> PostOrder;

{TIME_REGION(XXX, "td:Compute postorder");

  // Calculate top-down from main...
  if (Function *F = M.getFunction("main"))
    ComputePostOrder(*F, VisitedGraph, PostOrder);

  // Next calculate the graphs for each unreachable function...
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
    if (!I->isDeclaration())
      ComputePostOrder(*I, VisitedGraph, PostOrder);

  VisitedGraph.clear();   // Release memory!
}

{TIME_REGION(XXX, "td:Inline stuff");

  // Visit each of the graphs in reverse post-order now!
  while (!PostOrder.empty()) {
    InlineCallersIntoGraph(PostOrder.back());
    PostOrder.pop_back();
  }
}

  // Free the IndCallMap.
  while (!IndCallMap.empty()) {
    delete IndCallMap.begin()->second;
    IndCallMap.erase(IndCallMap.begin());
  }

  formGlobalECs();

  ExternallyCallable.clear();
  GlobalsGraph->removeTriviallyDeadNodes();
  GlobalsGraph->computeExternalFlags(DSGraph::DontMarkFormalsExternal);
  GlobalsGraph->computeIntPtrFlags();

  // Make sure each graph has updated external information about globals
  // in the globals graph.
  VisitedGraph.clear();
  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    if (!(F->isDeclaration())){
      DSGraph *Graph  = getOrCreateGraph(F);
      if (!VisitedGraph.insert(Graph).second) continue;

      cloneGlobalsInto(Graph, DSGraph::DontCloneCallNodes |
                        DSGraph::DontCloneAuxCallNodes);

      Graph->computeExternalFlags(DSGraph::DontMarkFormalsExternal);
      Graph->computeIntPtrFlags();
      // Clean up uninteresting nodes
      Graph->removeDeadNodes(0);

    }
  }

  // CBU contains the correct call graph.
  // Restore it, so that subsequent passes and clients can get it.
  restoreCorrectCallGraph();
  return false;
}


void TDDataStructures::ComputePostOrder(const Function &F,
                                        DenseSet<DSGraph*> &Visited,
                                        std::vector<DSGraph*> &PostOrder) {
  if (F.isDeclaration()) return;
  DSGraph* G = getOrCreateGraph(&F);
  if (!Visited.insert(G).second) return;

  // Recursively traverse all of the callee graphs.
  svset<const Function*> Callees;

  // Go through all of the callsites in this graph and find all callees
  // Here we're trying to capture all possible callees so that we can ensure
  // each function has all possible callers inlined into it.
  for (DSGraph::fc_iterator CI = G->fc_begin(), E = G->fc_end();
       CI != E; ++CI) {
    // Direct calls are easy, no reason to look at DSCallGraph
    // or anything to do with SCC's
    if (CI->isDirectCall()) {
      ComputePostOrder(*CI->getCalleeFunc(), Visited, PostOrder);
    }
    else {
      // Otherwise, ask the DSCallGraph for the full set of possible
      // callees for this callsite.
      // This includes all members of the SCC's of those callees,
      // and well as others in F's SCC, since we must assume
      // any indirect call might be intra-SCC.
      callgraph.addFullFunctionSet(CI->getCallSite(), Callees);
    }
  }

  for (svset<const Function*>::iterator I = Callees.begin(),
       E = Callees.end(); I != E; ++I)
    ComputePostOrder(**I, Visited, PostOrder);

  PostOrder.push_back(G);
}

/// InlineCallersIntoGraph - Inline all of the callers of the specified DS graph
/// into it, then recompute completeness of nodes in the resultant graph.
void TDDataStructures::InlineCallersIntoGraph(DSGraph* DSG) {
  // Inline caller graphs into this graph.  First step, get the list of call
  // sites that call into this graph.
  std::vector<CallerCallEdge> EdgesFromCaller;
  std::map<DSGraph*, std::vector<CallerCallEdge> >::iterator
    CEI = CallerEdges.find(DSG);
  if (CEI != CallerEdges.end()) {
    std::swap(CEI->second, EdgesFromCaller);
    CallerEdges.erase(CEI);
  }

  // Sort the caller sites to provide a by-caller-graph ordering.
  std::sort(EdgesFromCaller.begin(), EdgesFromCaller.end());


  // Merge information from the globals graph into this graph.  FIXME: This is
  // stupid.  Instead of us cloning information from the GG into this graph,
  // then having RemoveDeadNodes clone it back, we should do all of this as a
  // post-pass over all of the graphs.  We need to take cloning out of
  // removeDeadNodes and gut removeDeadNodes at the same time first though. :(
  cloneGlobalsInto(DSG, DSGraph::DontCloneCallNodes |
                        DSGraph::DontCloneAuxCallNodes);

  DEBUG(errs() << "[TD] Inlining callers into '"
        << DSG->getFunctionNames() << "'\n");

  DSG->maskIncompleteMarkers();
  // Iteratively inline caller graphs into this graph.
  while (!EdgesFromCaller.empty()) {
    DSGraph* CallerGraph = EdgesFromCaller.back().CallerGraph;

    // Iterate through all of the call sites of this graph, cloning and merging
    // any nodes required by the call.
    ReachabilityCloner RC(DSG, CallerGraph,
                          DSGraph::DontCloneCallNodes |
                          DSGraph::DontCloneAuxCallNodes);

    // Inline all call sites from this caller graph.
    do {
      const DSCallSite &CS = *EdgesFromCaller.back().CS;
      const Function &CF = *EdgesFromCaller.back().CalledFunction;
      DEBUG(errs() << "   [TD] Inlining graph into Fn '"
            << CF.getName().str() << "' from ");
      if (CallerGraph->getReturnNodes().empty()) {
        DEBUG(errs() << "SYNTHESIZED INDIRECT GRAPH");
      } else {
        DEBUG(errs() << "Fn '" << CS.getCallSite().getInstruction()->
              getParent()->getParent()->getName().str() << "'");
      }
      DEBUG(errs() << ": " << CF.getFunctionType()->getNumParams()
            << " args\n");

      // Get the formal argument and return nodes for the called function and
      // merge them with the cloned subgraph.
      DSCallSite T1 = DSG->getCallSiteForArguments(CF);
      RC.mergeCallSite(T1, CS);
      ++NumTDInlines;

      EdgesFromCaller.pop_back();
    } while (!EdgesFromCaller.empty() &&
             EdgesFromCaller.back().CallerGraph == CallerGraph);
  }



  // Next, now that this graph is finalized, we need to recompute the
  // incompleteness markers for this graph and remove unreachable nodes.

  // If any of the functions is externally callable, treat everything in its
  // SCC as externally callable.
  bool isExternallyCallable = false;
  for (DSGraph::retnodes_iterator I = DSG->retnodes_begin(),
         E = DSG->retnodes_end(); I != E; ++I)
    if (ExternallyCallable.count(I->first)) {
      isExternallyCallable = true;
      break;
    }

  // Recompute the Incomplete markers.  Depends on whether args are complete
  unsigned IncFlags = DSGraph::IgnoreFormalArgs;
  IncFlags |= DSGraph::IgnoreGlobals | DSGraph::MarkVAStart;
  DSG->markIncompleteNodes(IncFlags);

  // If this graph contains functions that are externally callable, now is the time to mark
  // their arguments and return values as external.  At this point TD is inlining all caller information,
  // and that means External callers too.
  unsigned ExtFlags
    = isExternallyCallable ? DSGraph::MarkFormalsExternal : DSGraph::DontMarkFormalsExternal;
  DSG->computeExternalFlags(ExtFlags);
  DSG->computeIntPtrFlags();

  cloneIntoGlobals(DSG, DSGraph::DontCloneCallNodes |
                        DSGraph::DontCloneAuxCallNodes);
  //
  // Delete dead nodes.  Treat globals that are unreachable as dead also.
  //
  // FIXME:
  //  Do not delete unreachable globals as the comment describes.  For its
  //  alignment checks on the results of load instructions, SAFECode must be
  //  able to find the DSNode of both the result of the load as well as the
  //  pointer dereferenced by the load.  If we remove unreachable globals, then
  //  if the dereferenced pointer is a global, its DSNode will not reachable
  //  from the local graph's scalar map, and chaos ensues.
  //
  //  So, for now, just remove dead nodes but leave the globals alone.
  //
  DSG->removeDeadNodes(0);

  // We are done with computing the current TD Graph!  Finally, before we can
  // finish processing this function, we figure out which functions it calls and
  // records these call graph edges, so that we have them when we process the
  // callee graphs.
  if (DSG->fc_begin() == DSG->fc_end()) return;

  // Loop over all the call sites and all the callees at each call site, and add
  // edges to the CallerEdges structure for each callee.
  for (DSGraph::fc_iterator CI = DSG->fc_begin(), E = DSG->fc_end();
       CI != E; ++CI) {

    // Handle direct calls efficiently.
    if (CI->isDirectCall()) {
      if (!CI->getCalleeFunc()->isDeclaration() &&
          !DSG->getReturnNodes().count(CI->getCalleeFunc()))
        CallerEdges[getOrCreateGraph(CI->getCalleeFunc())]
          .push_back(CallerCallEdge(DSG, &*CI, CI->getCalleeFunc()));
      continue;
    }

    svset<const Function*> AllCallees;
    std::vector<const Function*> Callees;

    // Get the list of callees
    callgraph.addFullFunctionSet(CI->getCallSite(), AllCallees);

    // Filter all non-declarations, and calls within this DSGraph
    for (svset<const Function*>::iterator I = AllCallees.begin(),
        E = AllCallees.end(); I != E; ++I) {
      const Function *F = *I;
      if (!F->isDeclaration() && getDSGraph(**I) != DSG)
        Callees.push_back(F);
    }
    AllCallees.clear();

    // If there is exactly one callee from this call site, remember the edge in
    // CallerEdges.
    if (Callees.size() == 1) {
      const Function * Callee = Callees[0];
      CallerEdges[getOrCreateGraph(Callee)]
          .push_back(CallerCallEdge(DSG, &*CI, Callee));
    }
    if (Callees.size() <= 1) continue;

    // Otherwise, there are multiple callees from this call site, so it must be
    // an indirect call.  Chances are that there will be other call sites with
    // this set of targets.  If so, we don't want to do M*N inlining operations,
    // so we build up a new, private, graph that represents the calls of all
    // calls to this set of functions.

    std::map<std::vector<const Function*>, DSGraph*>::iterator IndCallRecI =
      IndCallMap.lower_bound(Callees);

    // If we already have this graph, recycle it.
    if (IndCallRecI != IndCallMap.end() && IndCallRecI->first == Callees) {
      DEBUG(errs() << "  [TD] *** Reuse of indcall graph for " << Callees.size()
            << " callees!\n");
      DSGraph * IndCallGraph = IndCallRecI->second;
      assert(IndCallGraph->getFunctionCalls().size() == 1);

      // Merge the call into the CS already in the IndCallGraph
      ReachabilityCloner RC(IndCallGraph, DSG, 0);
      RC.mergeCallSite(IndCallGraph->getFunctionCalls().front(), *CI);
    } else {
      // Otherwise, create a new DSGraph to represent this.
      DSGraph* IndCallGraph = new DSGraph(DSG->getGlobalECs(),
                                          DSG->getDataLayout(), *TypeSS);

      // Clone over the call into the new DSGraph
      ReachabilityCloner RC(IndCallGraph, DSG, 0);
      DSCallSite ClonedCS = RC.cloneCallSite(*CI);

      // Add the cloned CS to the graph, as if it were an original call.
      IndCallGraph->getFunctionCalls().push_back(ClonedCS);

      // Save this graph for use later, should we need it.
      IndCallRecI = IndCallMap.insert(IndCallRecI,
                                      std::make_pair(Callees, IndCallGraph));

      // Additionally, make sure that each of the callees inlines this graph
      // exactly once.
      DSCallSite *NCS = &IndCallGraph->getFunctionCalls().front();
      for (unsigned i = 0, e = Callees.size(); i != e; ++i) {
        DSGraph* CalleeGraph = getDSGraph(*Callees[i]);
        if (CalleeGraph != DSG)
          CallerEdges[CalleeGraph].push_back(CallerCallEdge(IndCallGraph, NCS,
                                                            Callees[i]));
      }
    }
  }
}
