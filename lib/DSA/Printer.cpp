//===- Printer.cpp - Code for printing data structure graphs nicely -------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the 'dot' graph printer.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "dsgraph-printer"

#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "dsa/DSGraphTraits.h"
#include "llvm/Module.h"
#include "llvm/Constants.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Config/config.h"
#include "llvm/Support/FormattedStream.h"
#include <sstream>
using namespace llvm;

// OnlyPrintMain - The DataStructure printer exposes this option to allow
// printing of only the graph for "main".
//
namespace {
  cl::list<std::string> OnlyPrint("dsa-only-print", cl::ReallyHidden);
  cl::opt<bool> DontPrintGraphs("dont-print-ds", cl::ReallyHidden);
  cl::opt<bool> LimitPrint("dsa-limit-print", cl::Hidden);
  STATISTIC (MaxGraphSize   , "Maximum graph size");
  STATISTIC (NumFoldedNodes , "Number of folded nodes (in final graph)");
}

void DSNode::dump() const { print(errs(), 0); }
void DSNode::dumpParentGraph() const { getParentGraph()->dump(); }

static std::string getCaption(const DSNode *N, const DSGraph *G) {
  std::string empty;
  raw_string_ostream OS(empty);
  const Module *M = 0;

  if (!G) G = N->getParentGraph();

  // Get the module from ONE of the functions in the graph it is available.
  if (G && G->retnodes_begin() != G->retnodes_end())
    M = G->retnodes_begin()->first->getParent();
  if (M == 0 && G) {
    // If there is a global in the graph, we can use it to find the module.
    const DSScalarMap &SM = G->getScalarMap();
    if (SM.global_begin() != SM.global_end())
      M = (*SM.global_begin())->getParent();
  }

  if (N->isNodeCompletelyFolded())
    OS << "COLLAPSED";
  else {
    if (N->type_begin() != N->type_end())
      for (DSNode::TyMapTy::const_iterator ii = N->type_begin(),
           ee = N->type_end(); ii != ee; ++ii) {
        OS << ii->first << ": ";
        if (ii->second)
          for (svset<Type*>::const_iterator ni = ii->second->begin(),
               ne = ii->second->end(); ni != ne; ++ni) {
            Type * t = *ni;
            t->print (OS);
            OS << ", ";
          }
        else
          OS << "VOID";
        OS << " ";
      }
    else
      OS << "VOID";
    if (N->isArrayNode())
      OS << " array";
  }
  if (unsigned NodeType = N->getNodeFlags()) {
    OS << ": ";
    if (NodeType & DSNode::AllocaNode       ) OS << "S";
    if (NodeType & DSNode::HeapNode         ) OS << "H";
    if (NodeType & DSNode::GlobalNode       ) OS << "G";
    if (NodeType & DSNode::UnknownNode      ) OS << "U";
    if (NodeType & DSNode::IncompleteNode   ) OS << "I";
    if (NodeType & DSNode::ModifiedNode     ) OS << "M";
    if (NodeType & DSNode::ReadNode         ) OS << "R";
    if (NodeType & DSNode::ExternalNode     ) OS << "E";
    if (NodeType & DSNode::ExternFuncNode   ) OS << "X";
    if (NodeType & DSNode::IntToPtrNode     ) OS << "P";
    if (NodeType & DSNode::PtrToIntNode     ) OS << "2";
    if (NodeType & DSNode::VAStartNode      ) OS << "V";

#ifndef NDEBUG
    if (NodeType & DSNode::DeadNode       ) OS << "<dead>";
#endif
    OS << "\n";
  }

  //Indicate if this is a VANode for some function
  for (DSGraph::vanodes_iterator I = G->vanodes_begin(), E = G->vanodes_end();
      I != E; ++I) {
    DSNodeHandle VANode = I->second;
    if (N == VANode.getNode()) {
      OS << "(VANode for " << I->first->getName().str() << ")\n";
    }
  }

  EquivalenceClasses<const GlobalValue*> *GlobalECs = 0;
  if (G) GlobalECs = &G->getGlobalECs();

  for (DSNode::globals_iterator i = N->globals_begin(), e = N->globals_end(); 
       i != e; ++i) {
    WriteAsOperand(OS, *i, false, M);

    // Figure out how many globals are equivalent to this one.
    if (GlobalECs) {
      EquivalenceClasses<const GlobalValue*>::iterator I =
        GlobalECs->findValue(*i);
      if (I != GlobalECs->end()) {
        unsigned NumMembers =
          std::distance(GlobalECs->member_begin(I), GlobalECs->member_end());
        if (NumMembers != 1) OS << " + " << (NumMembers-1) << " EC";
      }
    }
    OS << "\n";
  }

  return OS.str();
}

namespace llvm {
template<>
struct DOTGraphTraits<const DSGraph*> : public DefaultDOTGraphTraits {
  DOTGraphTraits(bool& b) {}
  DOTGraphTraits() {}
  static std::string getGraphName(const DSGraph *G) {
    switch (G->getReturnNodes().size()) {
    case 0: return G->getFunctionNames();
    case 1: return "Function " + G->getFunctionNames();
    default: return "Functions: " + G->getFunctionNames();
    }
  }

  static std::string
  getNodeLabel(const DSNode* Node, const DSGraph *Graph) {
    return getCaption(Node, Graph);
  }

  static std::string getNodeAttributes(const DSNode *N, const DSGraph *Graph) {
    return "shape=Mrecord";
  }

  static bool edgeTargetsEdgeSource(const void *Node,
                                    DSNode::const_iterator I) {
    if (I.getOffset() < I->getSize()) {
      if (I->hasLink (I.getOffset())) {
        unsigned O = I->getLink(I.getOffset()).getOffset();
        return O != 0;
      } else {
        return false;
      }
    } else {
      return false;
    }
  }

  static std::string getEdgeSourceLabel(const void* Node,
                                        DSNode::const_iterator I) {
    std::string S;
    llvm::raw_string_ostream O(S);
    O << I.getOffset();
    return O.str();
  }

  static DSNode::const_iterator getEdgeTarget(const DSNode *Node,
                                              DSNode::const_iterator I) {
    unsigned O = I->getLink(I.getOffset()).getOffset();
    unsigned LinkNo = O;
    const DSNode *N = *I;
    DSNode::const_iterator R = N->begin();
    for (; LinkNo; --LinkNo)
      ++R;
    return R;
  }


  /// addCustomGraphFeatures - Use this graph writing hook to emit call nodes
  /// and the return node.
  ///
  static void addCustomGraphFeatures(const DSGraph *G,
                                     GraphWriter<const DSGraph*> &GW) {
    const Module *CurMod = 0;
    if (G->retnodes_begin() != G->retnodes_end())
      CurMod = G->retnodes_begin()->first->getParent();
    else {
      // If there is a global in the graph, we can use it to find the module.
      const DSScalarMap &SM = G->getScalarMap();
      if (SM.global_begin() != SM.global_end())
        CurMod = (*SM.global_begin())->getParent();
    }


    if (!LimitPrint) {
      // Add scalar nodes to the graph...
      const DSGraph::ScalarMapTy &VM = G->getScalarMap();
      for (DSGraph::ScalarMapTy::const_iterator I = VM.begin();
           I != VM.end(); ++I)
        if (!isa<GlobalValue>(I->first)) {
          std::string OS_str;
          llvm::raw_string_ostream OS(OS_str);
          WriteAsOperand(OS, I->first, false, CurMod);
          GW.emitSimpleNode(I->first, "", OS.str());
          
          // Add edge from return node to real destination
          DSNode *DestNode = I->second.getNode();
          int EdgeDest = I->second.getOffset();
          if (EdgeDest == 0) EdgeDest = -1;
          GW.emitEdge(I->first, -1, DestNode,
                      EdgeDest, "arrowtail=tee,color=gray63");
        }
    }


    // Output the returned value pointer...
    for (DSGraph::retnodes_iterator I = G->retnodes_begin(),
           E = G->retnodes_end(); I != E; ++I)
      if (I->second.getNode()) {
        std::string Label;
        if (G->getReturnNodes().size() == 1)
          Label = "returning";
        else
          Label = I->first->getName().str() + " ret node";
        // Output the return node...
        GW.emitSimpleNode(const_cast<Function*>(I->first), "plaintext=circle", Label);

        // Add edge from return node to real destination
        DSNode *RetNode = I->second.getNode();
        int RetEdgeDest = I->second.getOffset();
        if (RetEdgeDest == 0) RetEdgeDest = -1;
        GW.emitEdge(const_cast<Function*>(I->first), -1, RetNode,
                    RetEdgeDest, "arrowtail=tee,color=gray63");
      }

    // Output all of the call nodes...
    const DSGraph::FunctionListTy &FCs =
      G->shouldUseAuxCalls() ? G->getAuxFunctionCalls()
      : G->getFunctionCalls();
    for (DSGraph::FunctionListTy::const_iterator I = FCs.begin(), E = FCs.end();
         I != E; ++I) {
      const DSCallSite &Call = *I;
      std::vector<std::string> EdgeSourceCaptions(Call.getNumPtrArgs()+2);
      EdgeSourceCaptions[0] = "r";
      if (Call.isDirectCall())
        EdgeSourceCaptions[1] = Call.getCalleeFunc()->getName();
      else
        EdgeSourceCaptions[1] = "f";

      GW.emitSimpleNode(&Call, "shape=record", "call", Call.getNumPtrArgs()+2,
                        &EdgeSourceCaptions);

      if (DSNode *N = Call.getRetVal().getNode()) {
        int EdgeDest = Call.getRetVal().getOffset();
        if (EdgeDest == 0) EdgeDest = -1;
        GW.emitEdge(&Call, 0, N, EdgeDest, "color=gray63,tailclip=false");
      }

      // FIXME: visualize the VANode?

      // Print out the callee...
      if (Call.isIndirectCall()) {
        DSNode *N = Call.getCalleeNode();
        assert(N && "Null call site callee node!");
        GW.emitEdge(&Call, 1, N, -1, "color=gray63,tailclip=false");
      }

      for (unsigned j = 0, e = Call.getNumPtrArgs(); j != e; ++j)
        if (DSNode *N = Call.getPtrArg(j).getNode()) {
          int EdgeDest = Call.getPtrArg(j).getOffset();
          if (EdgeDest == 0) EdgeDest = -1;
          GW.emitEdge(&Call, j+2, N, EdgeDest, "color=gray63,tailclip=false");
        }
    }
  }
};
}   // end namespace llvm

void DSNode::print(llvm::raw_ostream &O, const DSGraph *G) const {
  GraphWriter<const DSGraph *> W(O, G, false);
  W.writeNode(this);
}

void DSGraph::print(llvm::raw_ostream &O) const {
  WriteGraph(O, this, "DataStructures");
}

void DSGraph::writeGraphToFile(llvm::raw_ostream &O,
                               const std::string &GraphName) const {
  std::string Filename = GraphName + ".dot";
  O << "Writing '" << Filename << "'...";
  if (!DontPrintGraphs) {
    std::string Error;
    llvm::raw_fd_ostream F(Filename.c_str(), Error);

    if (Error.size()) {
      O << "  error opening file for writing! " << Error << "\n";
      return;
    }

    print(F);
  } else {
    O << "(disabled by command-line flag)";
  }
  unsigned NumCalls = shouldUseAuxCalls() ?
    getAuxFunctionCalls().size() : getFunctionCalls().size();
  O << " [" << getGraphSize() << "+" << NumCalls << "]\n";
}

/// viewGraph - Emit a dot graph, run 'dot', run gv on the postscript file,
/// then cleanup.  For use from the debugger.
///
void DSGraph::viewGraph() const {
  ViewGraph(this, "ds.tempgraph", "DataStructures");
}


template <typename Collection>
static void printCollection(const Collection &C, llvm::raw_ostream &O,
                            const Module *M, const std::string &Prefix) {
  if (M == 0) {
    O << "Null Module pointer, cannot continue!\n";
    return;
  }

  unsigned TotalNumNodes = 0, TotalCallNodes = 0;
  for (Module::const_iterator I = M->begin(), E = M->end(); I != E; ++I)
    if (C.hasDSGraph(*I)) {
      DSGraph* Gr = C.getDSGraph((const Function&)*I);
      unsigned NumCalls = Gr->shouldUseAuxCalls() ?
        Gr->getAuxFunctionCalls().size() : Gr->getFunctionCalls().size();
      bool IsDuplicateGraph = false;

      //if no only print options, print everything
      bool doPrint = OnlyPrint.begin() == OnlyPrint.end();
      //otherwise check the name
      if (!doPrint)
        doPrint = OnlyPrint.end() !=
        std::find(OnlyPrint.begin(), OnlyPrint.end(), I->getName().str());

      if (doPrint) {
        const Function *SCCFn = Gr->retnodes_begin()->first;
        if (&*I == SCCFn) {
          Gr->writeGraphToFile(O, Prefix+I->getName().str());
        } else {
          IsDuplicateGraph = true; // Don't double count node/call nodes.
          O << "Didn't write '" << Prefix+I->getName().str()
            << ".dot' - Graph already emitted to '" << Prefix+SCCFn->getName().str()
            << "\n";
        }
      } else {
        const Function *SCCFn = Gr->retnodes_begin()->first;
        if (&*I == SCCFn) {
          //O << "Skipped Writing '" << Prefix+I->getName().str() << ".dot'... ["
          //  << Gr->getGraphSize() << "+" << NumCalls << "]\n";
        } else {
          IsDuplicateGraph = true; // Don't double count node/call nodes.
        }
      }

      if (!IsDuplicateGraph) {
        unsigned GraphSize = Gr->getGraphSize();
        if (MaxGraphSize < GraphSize) MaxGraphSize = GraphSize;

        TotalNumNodes += Gr->getGraphSize();
        TotalCallNodes += NumCalls;
        for (DSGraph::node_iterator NI = Gr->node_begin(), E = Gr->node_end();
             NI != E; ++NI)
          if (NI->isNodeCompletelyFolded())
            ++NumFoldedNodes;
      }
    }

  DSGraph* GG = C.getGlobalsGraph();
  TotalNumNodes  += GG->getGraphSize();
  TotalCallNodes += GG->getFunctionCalls().size();
  GG->writeGraphToFile(O, Prefix + "GlobalsGraph");

  O << "\nGraphs contain [" << TotalNumNodes << "+" << TotalCallNodes
    << "] nodes total\n";
}


void DataStructures::dumpCallGraph() const {
  for (DSCallGraph::flat_key_iterator ki = callgraph.flat_key_begin(),
       ke = callgraph.flat_key_end(); ki != ke; ++ki) {
    errs() << (*ki)->getName() << ": [";
    for (DSCallGraph::flat_iterator cbi = callgraph.flat_callee_begin(*ki),
         cbe = callgraph.flat_callee_end(*ki); cbi != cbe; ++cbi)
      errs() << (*cbi)->getName() << " ";
    errs() << "]\n";
  }
}

// print - Print out the analysis results...
void DataStructures::print(llvm::raw_ostream &O, const Module *M) const {
  if (handleTest(O, M)) return;

  printCollection(*this, O, M, printname);
  //dumpCallGraph();
}
