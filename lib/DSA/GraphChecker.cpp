//===- GraphChecker.cpp - Assert that various graph properties hold -------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass is used to test DSA with regression tests.  It can be used to check
// that certain graph properties hold, such as two nodes being disjoint, whether
// or not a node is collapsed, etc.  These are the command line arguments that
// it supports:
//
//   --dsgc-dspass={local,bu,td}      - Specify what flavor of graph to check
//   --dsgc-abort-if-any-collapsed    - Abort if any collapsed nodes are found
//   --dsgc-abort-if-collapsed=<list> - Abort if a node pointed to by an SSA
//                                      value with name in <list> is collapsed
//   --dsgc-check-flags=<list>        - Abort if the specified nodes have flags
//                                      that are not specified.
//   --dsgc-abort-if-merged=<list>    - Abort if any of the named SSA values
//                                      point to the same node.
//
//===----------------------------------------------------------------------===//

#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/IR/Value.h"
#include <set>
using namespace llvm;

namespace {
  enum DSPass { local, bu, td };
  cl::opt<DSPass>
  DSPass("dsgc-dspass", cl::Hidden,
         cl::desc("Specify which DSA pass the -datastructure-gc pass should use"),
         cl::values(clEnumVal(local, "Local pass"),
                    clEnumVal(bu,    "Bottom-up pass"),
                    clEnumVal(td,    "Top-down pass")),
         cl::init(local));

  cl::opt<bool>
  AbortIfAnyCollapsed("dsgc-abort-if-any-collapsed", cl::Hidden,
                      cl::desc("Abort if any collapsed nodes are found"));
  cl::list<std::string>
  AbortIfCollapsed("dsgc-abort-if-collapsed", cl::Hidden, cl::CommaSeparated,
                   cl::desc("Abort if any of the named symbols is collapsed"));
  cl::list<std::string>
  CheckFlags("dsgc-check-flags", cl::Hidden, cl::CommaSeparated,
             cl::desc("Check that flags are specified for nodes"));
  cl::list<std::string>
  AbortIfMerged("dsgc-abort-if-merged", cl::Hidden, cl::CommaSeparated,
             cl::desc("Abort if any of the named symbols are merged together"));

  struct DSGC : public FunctionPass {
    static char ID;
    DSGC();
    bool doFinalization(Module &M);
    bool runOnFunction(Function &F);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      switch (DSPass) {
      case local: AU.addRequired<LocalDataStructures>(); break;
      case bu:    AU.addRequired<BUDataStructures>(); break;
      case td:    AU.addRequired<TDDataStructures>(); break;
      }
      AU.setPreservesAll();
    }
    void print(llvm::raw_ostream &O, const Module *M) const {}

  private:
    void verify(const DSGraph* G);
  };

  RegisterPass<DSGC> X("datastructure-gc", "DSA Graph Checking Pass");
}

char DSGC::ID;

FunctionPass *llvm::createDataStructureGraphCheckerPass() {
  return new DSGC();
}


DSGC::DSGC() : FunctionPass(ID) {
  if (!AbortIfAnyCollapsed && AbortIfCollapsed.empty() &&
      CheckFlags.empty() && AbortIfMerged.empty()) {
    errs() << "The -datastructure-gc is useless if you don't specify any"
            << " -dsgc-* options.  See the -help-hidden output for a list.\n";
    abort();
  }
}


/// doFinalization - Verify that the globals graph is in good shape...
///
bool DSGC::doFinalization(Module &M) {
  switch (DSPass) {
  case local:verify(getAnalysis<LocalDataStructures>().getGlobalsGraph());break;
  case bu:   verify(getAnalysis<BUDataStructures>().getGlobalsGraph()); break;
  case td:   verify(getAnalysis<TDDataStructures>().getGlobalsGraph()); break;
  }
  return false;
}

/// runOnFunction - Get the DSGraph for this function and verify that it is ok.
///
bool DSGC::runOnFunction(Function &F) {
  switch (DSPass) {
  case local: verify(getAnalysis<LocalDataStructures>().getDSGraph(F)); break;
  case bu:    verify(getAnalysis<BUDataStructures>().getDSGraph(F)); break;
  case td:    verify(getAnalysis<TDDataStructures>().getDSGraph(F)); break;
  }

  return false;
}

/// verify - This is the function which checks to make sure that all of the
/// invariants established on the command line are true.
///
void DSGC::verify(const DSGraph* G) {
  // Loop over all of the nodes, checking to see if any are collapsed...
  if (AbortIfAnyCollapsed) {
    for (DSGraph::node_const_iterator I = G->node_begin(), E = G->node_end();
         I != E; ++I)
      if (I->isNodeCompletelyFolded()) {
        errs() << "Node is collapsed: ";
        I->print(errs(), G);
        abort();
      }
  }

  if (!AbortIfCollapsed.empty() || !CheckFlags.empty() ||
      !AbortIfMerged.empty()) {
    // Convert from a list to a set, because we don't have cl::set's yet.  FIXME
    std::set<std::string> AbortIfCollapsedS(AbortIfCollapsed.begin(),
                                            AbortIfCollapsed.end());
    std::set<std::string> AbortIfMergedS(AbortIfMerged.begin(),
                                         AbortIfMerged.end());
    std::map<std::string, unsigned> CheckFlagsM;

    for (cl::list<std::string>::iterator I = CheckFlags.begin(),
           E = CheckFlags.end(); I != E; ++I) {
      std::string::size_type ColonPos = I->rfind(':');
      if (ColonPos == std::string::npos) {
        errs() << "Error: '" << *I
               << "' is an invalid value for the --dsgc-check-flags option!\n";
        abort();
      }

      unsigned Flags = 0;
      for (unsigned C = ColonPos+1; C != I->size(); ++C)
        switch ((*I)[C]) {
        case 'S': Flags |= DSNode::AllocaNode;      break;
        case 'H': Flags |= DSNode::HeapNode;        break;
        case 'G': Flags |= DSNode::GlobalNode;      break;
        case 'U': Flags |= DSNode::UnknownNode;     break;
        case 'I': Flags |= DSNode::IncompleteNode;  break;
        case 'M': Flags |= DSNode::ModifiedNode;    break;
        case 'R': Flags |= DSNode::ReadNode;        break;
        case 'A': Flags |= DSNode::ArrayNode;       break;
        default: errs() << "Invalid DSNode flag!\n"; abort();
        }
      CheckFlagsM[std::string(I->begin(), I->begin()+ColonPos)] = Flags;
    }

    // Now we loop over all of the scalars, checking to see if any are collapsed
    // that are not supposed to be, or if any are merged together.
    const DSGraph::ScalarMapTy &SM = G->getScalarMap();
    std::map<DSNode*, std::string> AbortIfMergedNodes;

    for (DSGraph::ScalarMapTy::const_iterator I = SM.begin(), E = SM.end();
         I != E; ++I)
      if (I->first->hasName() && I->second.getNode()) {
        const std::string &Name = I->first->getName();
        DSNode *N = I->second.getNode();

        // Verify it is not collapsed if it is not supposed to be...
        if (N->isNodeCompletelyFolded() && AbortIfCollapsedS.count(Name)) {
          errs() << "Node for value '%" << Name << "' is collapsed: ";
          N->print(errs(), G);
          abort();
        }

        if (CheckFlagsM.count(Name) && CheckFlagsM[Name] != N->getNodeFlags()) {
          errs() << "Node flags are not as expected for node: " << Name
                 << " (" << CheckFlagsM[Name] << ":" <<N->getNodeFlags()
                 << ")\n";
          N->print(errs(), G);
          abort();
        }

        // Verify that it is not merged if it is not supposed to be...
        if (AbortIfMergedS.count(Name)) {
          if (AbortIfMergedNodes.count(N)) {
            errs() << "Nodes for values '%" << Name << "' and '%"
                   << AbortIfMergedNodes[N] << "' is merged: ";
            N->print(errs(), G);
            abort();
          }
          AbortIfMergedNodes[N] = Name;
        }
      }
  }
}
