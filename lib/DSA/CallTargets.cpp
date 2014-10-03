//=- lib/Analysis/IPA/CallTargets.cpp - Resolve Call Targets --*- C++ -*-=====//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass uses DSA to map targets of all calls, and reports on if it
// thinks it knows all targets of a given call.
//
// Loop over all callsites, and lookup the DSNode for that site.  Pull the
// Functions from the node as callees.
// This is essentially a utility pass to simplify later passes that only depend
// on call sites and callees to operate (such as a devirtualizer).
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "call-targets"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "dsa/CallTargets.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/IR/Constants.h"
#include <ostream>
using namespace llvm;

RegisterPass<dsa::CallTargetFinder<EQTDDataStructures> > X("calltarget-eqtd","Find Call Targets (uses DSA-EQTD)");
RegisterPass<dsa::CallTargetFinder<TDDataStructures> > Y("calltarget-td","Find Call Targets (uses DSA-TD)");
namespace {
  STATISTIC (DirCall, "Number of direct calls");
  STATISTIC (IndCall, "Number of indirect calls");
  STATISTIC (CompleteInd, "Number of complete indirect calls");
  STATISTIC (CompleteEmpty, "Number of complete empty calls");

}

namespace dsa {
  template<typename dsa>
char CallTargetFinder<dsa>::ID = 0;

  template<class dsa>
void CallTargetFinder<dsa>::findIndTargets(Module &M)
{
  dsa* T = &getAnalysis<dsa>();
  const DSCallGraph & callgraph = T->getCallGraph();
  DSGraph* G = T->getGlobalsGraph();
  DSGraph::ScalarMapTy& SM = G->getScalarMap();
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
    if (!I->isDeclaration())
      for (Function::iterator F = I->begin(), FE = I->end(); F != FE; ++F)
        for (BasicBlock::iterator B = F->begin(), BE = F->end(); B != BE; ++B)
          if (isa<CallInst>(B) || isa<InvokeInst>(B)) {
            CallSite cs(B);
            AllSites.push_back(cs);
            Function* CF = cs.getCalledFunction();

            if (isa<UndefValue>(cs.getCalledValue())) continue;
            if (isa<InlineAsm>(cs.getCalledValue())) continue;

            //
            // If the called function is casted from one function type to
            // another, peer into the cast instruction and pull out the actual
            // function being called.
            //
            if (!CF)
              CF = dyn_cast<Function>(cs.getCalledValue()->stripPointerCasts());

            if (!CF) {
              Value * calledValue = cs.getCalledValue()->stripPointerCasts();
              if (isa<ConstantPointerNull>(calledValue)) {
                ++DirCall;
                CompleteSites.insert(cs);
              } else {
                IndCall++;

                DSCallGraph::callee_iterator csi = callgraph.callee_begin(cs),
                                   cse = callgraph.callee_end(cs);
                while(csi != cse) {
                  const Function *F = *csi;
                  DSCallGraph::scc_iterator sccii = callgraph.scc_begin(F),
                    sccee = callgraph.scc_end(F);
                  for(;sccii != sccee; ++sccii) {
                    DSGraph::ScalarMapTy::const_iterator I = SM.find(SM.getLeaderForGlobal(*sccii));
                    if (I != SM.end()) {
                      IndMap[cs].push_back (*sccii);
                    }
                  }
                  ++csi;
                }
                const Function *F1 = (cs).getInstruction()->getParent()->getParent();
                F1 = callgraph.sccLeader(&*F1);
                
                DSCallGraph::scc_iterator sccii = callgraph.scc_begin(F1),
                  sccee = callgraph.scc_end(F1);
                for(;sccii != sccee; ++sccii) {
                  DSGraph::ScalarMapTy::const_iterator I = SM.find(SM.getLeaderForGlobal(*sccii));
                  if (I != SM.end()) {
                    IndMap[cs].push_back (*sccii);
                  }
                }

                DSNode* N = T->getDSGraph(*cs.getCaller())
                  ->getNodeForValue(cs.getCalledValue()).getNode();
                assert (N && "CallTarget: findIndTargets: No DSNode!");

                if (!N->isIncompleteNode() && !N->isExternalNode() && IndMap[cs].size()) {
                  CompleteSites.insert(cs);
                  ++CompleteInd;
                } 
                if (!N->isIncompleteNode() && !N->isExternalNode() && !IndMap[cs].size()) {
                  ++CompleteEmpty;
                  DEBUG(errs() << "Call site empty: '"
                                << cs.getInstruction()->getName()
                                << "' In '"
                                << cs.getInstruction()->getParent()->getParent()->getName()
                                << "'\n");
                }
              }
            } else {
              ++DirCall;
              IndMap[cs].push_back(CF);
              CompleteSites.insert(cs);
            }
          }
}

  template<class dsa>
void CallTargetFinder<dsa>::print(llvm::raw_ostream &O, const Module *M) const
{
  O << "[* = incomplete] CS: func list\n";
  for (std::map<CallSite, std::vector<const Function*> >::const_iterator ii =
       IndMap.begin(),
         ee = IndMap.end(); ii != ee; ++ii) {

    if (ii->first.getCalledFunction())  //only print indirect
      continue;
    if(isa<Function>(ii->first.getCalledValue()->stripPointerCasts()))
      continue;
      if (!isComplete(ii->first)) {
        O << "* ";
        CallSite cs = ii->first;
        cs.getInstruction()->dump();
        O << cs.getInstruction()->getParent()->getParent()->getName().str() << " "
          << cs.getInstruction()->getName().str() << " ";
      }
      O << ii->first.getInstruction() << ":";
      for (std::vector<const Function*>::const_iterator i = ii->second.begin(),
             e = ii->second.end(); i != e; ++i) {
        O << " " << (*i)->getName().str();
      }
      O << "\n";
  }
}

  template<class dsa>
bool CallTargetFinder<dsa>::runOnModule(Module &M) {
  findIndTargets(M);
  return false;
}

  template<class dsa>
void CallTargetFinder<dsa>::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<dsa>();
}
}
