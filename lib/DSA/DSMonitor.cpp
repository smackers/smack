
#include "dsa/DSMonitor.h"
#include "dsa/DSGraph.h"
#include "llvm/IR/DebugInfo.h"
#include "smack/SmackOptions.h"

#include <deque>

namespace llvm {

// XXX duplicated from DSA/Printer.cpp XXX
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
    (*i)->printAsOperand(OS,false,M);

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

Instruction * getInstruction(Value *V) {
  std::set<Value*> covered{ V };
  std::deque<Value*> workList{ V };

  while (!workList.empty()) {
    V = workList.front();
    workList.pop_front();
    if (auto I = dyn_cast<Instruction>(V)) {
      return I;
    } else {
      for (auto U : V->users()) {
        if (covered.count(U) == 0) {
          workList.push_back(U);
          covered.insert(U);
        }
      }
    }
  }

  return nullptr;
}

void DSMonitor::unwatch() {
  if (!N.isNull())
    N.setTo(nullptr, 0);
  caption = "";
  location = "";
}

void DSMonitor::watch(DSNodeHandle N, std::vector<Value*> VS, std::string M) {
  if (N.isNull() || N.getNode()->isCollapsedNode()) {
    unwatch();
    return;
  }

  this->N = N;
  this->VS = VS;
  this->message = M;
  DSGraph *G = N.getNode()->getParentGraph();
  caption = getCaption(N.getNode(), G);

  if (!VS.empty()) {
    Instruction *I = getInstruction(VS[0]);
    if (I && I->getMetadata("dbg")) {
      const DebugLoc DL = I->getDebugLoc();
      auto *scope = cast<DIScope>(DL.getScope());
      location = scope->getFilename().str() + ":"
        + std::to_string(DL.getLine()) + ":"
        + std::to_string(DL.getCol());
    }
  }
}

void DSMonitor::warn() {
  if (!smack::SmackOptions::Warnings)
    return;

  if (location != "")
    errs() << location << ": ";

  errs() << "warning: collapsing DSA node\n";

  if (message != "")
    errs() << message << "\n";

  if (VS.empty()) {
    errs() << "(unknown value)" << "\n";

  } else {
    if (Instruction *I = getInstruction(VS[0])) {
      if (BasicBlock *B = I->getParent()) {
        if (Function *F = B->getParent()) {
          if (F->hasName())
            errs() << "in function:\n  " << F->getName() << "\n";
        }
        if (B->hasName())
          errs() << "in block:\n  " << I->getParent()->getName() << "\n";
      }
      errs() << "at instruction:\n" << *I << "\n";
    }

    for (auto V : VS)
      errs() << "at value:\n" << *V << "\n";

    if (caption != "")
      errs() << "node:\n  " << caption << "\n";
  }
  errs() << "\n";
}

void DSMonitor::witness(DSNodeHandle N, std::vector<Value*> VS, std::string M) {
  if (N.isNull() || N.getNode()->isCollapsedNode())
    return;

  watch(N,VS,M);
  check();
}

void DSMonitor::check() {
  if (!N.isNull() && N.getNode()->isCollapsedNode())
    warn();
  unwatch();
}

}
