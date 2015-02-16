//===- DataStructureStats.cpp - Various statistics for DS Graphs ----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines a little pass that prints out statistics for DS Graphs.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "DSStats"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "dsa/TypeSafety.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Pass.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FormattedStream.h"

#include <ostream>
using namespace llvm;

namespace {
  STATISTIC (TotalNumCallees, 
             "Total number of callee functions at all indirect call sites");
  STATISTIC (NumIndirectCalls, 
             "Total number of indirect call sites in the program");

  // Typed/Untyped memory accesses: If DSA can infer that the types the loads
  // and stores are accessing are correct (ie, the node has not been collapsed),
  // increment the appropriate counter.
  STATISTIC (NumTypedMemAccesses,
             "Number of loads/stores which are fully typed");
  STATISTIC (NumUntypedMemAccesses,
             "Number of loads/stores which are untyped");
  STATISTIC (NumTypeCount0Accesses,
             "Number of loads/stores which are access a DSNode with 0 type");
  STATISTIC (NumTypeCount1Accesses,
             "Number of loads/stores which are access a DSNode with 1 type");
  STATISTIC (NumTypeCount2Accesses,
             "Number of loads/stores which are access a DSNode with 2 type");
  STATISTIC (NumTypeCount3Accesses,
             "Number of loads/stores which are access a DSNode with 3 type");
  STATISTIC (NumTypeCount4Accesses,
             "Number of loads/stores which are access a DSNode with >3 type");
  STATISTIC (NumIncompleteAccesses,
             "Number of loads/stores which are on incomplete nodes");
  STATISTIC (NumUnknownAccesses,
             "Number of loads/stores which are on unknown nodes");
  STATISTIC (NumExternalAccesses,
             "Number of loads/stores which are on external nodes");
  STATISTIC (NumI2PAccesses,
             "Number of loads/stores which are on inttoptr nodes");
  STATISTIC (NumFoldedAccess,
             "Number of loads/stores which are on folded nodes");

  class DSGraphStats : public FunctionPass, public InstVisitor<DSGraphStats> {
    void countCallees(const Function &F);
    const TDDataStructures *DS;
    const DataLayout *TD;
    const DSGraph *TDGraph;
    dsa::TypeSafety<TDDataStructures> *TS;
    DSNodeHandle getNodeHandleForValue(Value *V);
    bool isNodeForValueUntyped(Value *V, unsigned offset, const Function *);
  public:
    static char ID;
    DSGraphStats() : FunctionPass(ID) {}

    /// Driver functions to compute the Load/Store Dep. Graph per function.
    bool runOnFunction(Function& F);

    /// getAnalysisUsage - This modify nothing, and uses the Top-Down Graph.
    void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
      AU.addRequired<TDDataStructures>();
      AU.addRequired<DataLayoutPass>();
      AU.addRequired<dsa::TypeSafety<TDDataStructures> >();
    }

    void visitLoad(LoadInst &LI);
    void visitStore(StoreInst &SI);

    /// Debugging support methods
    void print(llvm::raw_ostream &O, const Module* = 0) const { }
  };

  static RegisterPass<DSGraphStats> Z("dsstats", "DS Graph Statistics");
}

char DSGraphStats::ID;

FunctionPass *llvm::createDataStructureStatsPass() { 
  return new DSGraphStats();
}


static bool isIndirectCallee(Value *V) {
  if (isa<Function>(V)) return false;

  if (CastInst *CI = dyn_cast<CastInst>(V))
    return isIndirectCallee(CI->getOperand(0));

  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V))
    if (CE->isCast()) 
      return isIndirectCallee(CE->getOperand(0));

  if (GlobalAlias *GA = dyn_cast<GlobalAlias>(V)) {
    return isIndirectCallee(GA->getAliasee());
  }
  return true;
}


void DSGraphStats::countCallees(const Function& F) {
  const DSCallGraph callgraph = DS->getCallGraph();
  unsigned numIndirectCalls = 0, totalNumCallees = 0;

  for (DSGraph::fc_iterator I = TDGraph->fc_begin(), E = TDGraph->fc_end();
       I != E; ++I)
    if (isIndirectCallee(I->getCallSite().getCalledValue())) {
      // This is an indirect function call
      std::vector<const Function*> Callees;
      callgraph.addFullFunctionList(I->getCallSite(), Callees);

      if (Callees.size() > 0) {
        totalNumCallees  += Callees.size();
        ++numIndirectCalls;
      } else {
        DEBUG(errs() << "WARNING: No callee in Function '" 
              << F.getName().str() << " at call: \n"
              << *I->getCallSite().getInstruction());
      }
    }

  TotalNumCallees  += totalNumCallees;
  NumIndirectCalls += numIndirectCalls;

  if (numIndirectCalls) {
    DEBUG(errs() << "  In function " << F.getName() << ":  "
          << (totalNumCallees / (double) numIndirectCalls)
          << " average callees per indirect call\n");
  }
}

DSNodeHandle DSGraphStats::getNodeHandleForValue(Value *V) {
  const DSGraph *G = TDGraph;
  const DSGraph::ScalarMapTy &ScalarMap = G->getScalarMap();
  DSGraph::ScalarMapTy::const_iterator I = ScalarMap.find(V);
  if (I != ScalarMap.end())
    return I->second;

  G = TDGraph->getGlobalsGraph();
  const DSGraph::ScalarMapTy &GlobalScalarMap = G->getScalarMap();
  I = GlobalScalarMap.find(V);
  if (I != GlobalScalarMap.end())
    return I->second;

  return 0;
}

bool DSGraphStats::isNodeForValueUntyped(Value *V, unsigned Offset, const Function *F) {
  DSNodeHandle NH = getNodeHandleForValue(V);
  if(!NH.getNode()){
    return true;
  }
  else {
    DSNode *N = NH.getNode();
    if (N->isNodeCompletelyFolded()){
      ++NumFoldedAccess;
      return true;
    }
    if ( N->isExternalNode()){
      ++NumExternalAccesses;
      return true;
    }
    if ( N->isIncompleteNode()){
      ++NumIncompleteAccesses;
      return true;
    }
    if (N->isUnknownNode()){
      ++NumUnknownAccesses;
      return true;
    }
    if (N->isIntToPtrNode()){
      ++NumI2PAccesses;
      return true;
    }
    // it is a complete node, now check how many types are present
    int count = 0;
    unsigned offset = NH.getOffset() + Offset;
    if (N->type_begin() != N->type_end())
      for (DSNode::TyMapTy::const_iterator ii = N->type_begin(),
           ee = N->type_end(); ii != ee; ++ii) {
        if(ii->first != offset)
          continue;
        count += ii->second->size();
      }

    if (count ==0)
      ++NumTypeCount0Accesses;
    else if(count == 1)
      ++NumTypeCount1Accesses;
    else if(count == 2)
      ++NumTypeCount2Accesses;
    else if(count == 3)
      ++NumTypeCount3Accesses;
    else
      ++NumTypeCount4Accesses;
    DEBUG(assert(TS->isTypeSafe(V,F)));
  }
  return false;
}

void DSGraphStats::visitLoad(LoadInst &LI) {
  if (isNodeForValueUntyped(LI.getOperand(0), 0,LI.getParent()->getParent())) {
    NumUntypedMemAccesses++;
  } else {
    NumTypedMemAccesses++;
  }
}

void DSGraphStats::visitStore(StoreInst &SI) {
  if (isNodeForValueUntyped(SI.getOperand(1), 0,SI.getParent()->getParent())) {
    NumUntypedMemAccesses++;
  } else {
    NumTypedMemAccesses++;
  }
}

bool DSGraphStats::runOnFunction(Function& F) {
  DS = &getAnalysis<TDDataStructures>();
  TD = &getAnalysis<DataLayoutPass>().getDataLayout();
  TS = &getAnalysis<dsa::TypeSafety<TDDataStructures> >();
  TDGraph = DS->getDSGraph(F);
  countCallees(F);
  visit(F);
  return false;
}
