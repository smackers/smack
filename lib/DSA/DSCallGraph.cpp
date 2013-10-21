//===- DSCallGraph.cpp - Implement the Call Graph Support class -----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the Call Graph
//
//===----------------------------------------------------------------------===//

#include "dsa/DSCallGraph.h"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/CommandLine.h"

#include <algorithm>

using namespace llvm;

static bool _hasPointers(const llvm::FunctionType* T) {
  if (T->isVarArg()) return true;
  if (T->getReturnType()->isPointerTy()) return true;
  for (unsigned x = 0; x < T->getNumParams(); ++x)
    if (T->getParamType(x)->isPointerTy())
      return true;
  return false;
}

bool DSCallGraph::hasPointers(const llvm::Function* F) {
  return _hasPointers(F->getFunctionType());
}

bool DSCallGraph::hasPointers(llvm::CallSite& CS) {
  if (CS.getCalledFunction())
    return hasPointers(CS.getCalledFunction());

  const llvm::Value* Callee = CS.getCalledValue();
  const llvm::Type* T = Callee->getType();
  if (const llvm::PointerType* PT = llvm::dyn_cast<llvm::PointerType>(T))
    T = PT->getElementType();
  return _hasPointers(llvm::cast<llvm::FunctionType>(T));
}

unsigned DSCallGraph::tarjan_rec(const llvm::Function* F, TFStack& Stack,
                                 unsigned &NextID, TFMap& ValMap) {
  assert(!ValMap.count(F) && "Shouldn't revisit functions!");
  unsigned Min = NextID++, MyID = Min;
  ValMap[F] = Min;
  Stack.push_back(F);

  // The edges out of the current node are the call site targets...
  for (flat_iterator ii = flat_callee_begin(F),
       ee = flat_callee_end(F); ii != ee; ++ii) {
    unsigned M = Min;
    // Have we visited the destination function yet?
    TFMap::iterator It = ValMap.find(*ii);
    if (It == ValMap.end()) // No, visit it now.
      M = tarjan_rec(*ii, Stack, NextID, ValMap);
    else if (std::find(Stack.begin(), Stack.end(), *ii) != Stack.end())
      M = It->second;
    if (M < Min) Min = M;
  }

  assert(ValMap[F] == MyID && "SCC construction assumption wrong!");
  if (Min != MyID)
    return Min; // This is part of a larger SCC!

  // If this is a new SCC, process it now.
  if (F == Stack.back()) {
    // single node case
    Stack.pop_back();
    SCCs.insert(F);
  } else {
    // Take care that the leader is not an external function
    std::vector<const llvm::Function*> microSCC;
    const llvm::Function* NF = 0;
    const llvm::Function* Leader = 0;
    do {
      NF = Stack.back();
      Stack.pop_back();
      microSCC.push_back(NF);
      if (!Leader && !NF->isDeclaration()) Leader = NF;
    } while (NF != F);
    //Leader is not an extern function
    //No multi-function SCC can not have a defined function, as all externs
    //are treated as having no callees
    assert(Leader && "No Leader?");
    SCCs.insert(Leader);
    Leader = SCCs.getLeaderValue(Leader);
    assert(!Leader->isDeclaration() && "extern leader");
    for (std::vector<const llvm::Function*>::iterator ii = microSCC.begin(),
         ee = microSCC.end(); ii != ee; ++ii) {
      SCCs.insert(*ii);
      const llvm::Function* Temp = SCCs.getLeaderValue(*ii);
      //Order Matters
      SCCs.unionSets(Leader, Temp);
      assert (SCCs.getLeaderValue(Leader) == Leader && "SCC construction wrong");
      assert (SCCs.getLeaderValue(Temp) == Leader && "SCC construction wrong");
    }
  }

  return MyID;
}

void DSCallGraph::buildSCCs() {
  TFStack Stack;
  TFMap ValMap;
  unsigned NextID = 1;

  for (flat_key_iterator ii = flat_key_begin(), ee = flat_key_end();
       ii != ee; ++ii)
    if (!ValMap.count(*ii))
      tarjan_rec(*ii, Stack, NextID, ValMap);

  removeECFunctions();
}

static void removeECs(DSCallGraph::FuncSet& F,
                      llvm::EquivalenceClasses<const llvm::Function*>& ECs) {
  DSCallGraph::FuncSet result;
  for (DSCallGraph::FuncSet::const_iterator ii = F.begin(), ee = F.end();
       ii != ee; ++ii)
    result.insert(ECs.getLeaderValue(*ii));

  F.swap(result);
}

void DSCallGraph::removeECFunctions() {
  //First the callers
  for (SimpleCalleesTy::iterator ii = SimpleCallees.begin(),
       ee = SimpleCallees.end(); ii != ee;) {
    const llvm::Function* Leader = SCCs.getLeaderValue(ii->first);
    if (Leader == ii->first) {
      // This is the leader, leave it alone
      ++ii;
    } else {
      //This is not the leader, merge into the leader
      SimpleCallees[Leader].insert(ii->second.begin(), ii->second.end());
      SimpleCalleesTy::iterator tmpii = ii;
      ++ii;
      SimpleCallees.erase(tmpii);
    }
  }
  // then the callees
  for (SimpleCalleesTy::iterator ii = SimpleCallees.begin(),
       ee = SimpleCallees.end(); ii != ee; ++ii) {
    removeECs(ii->second, SCCs);
    //and apparent self loops inside an SCC
    ii->second.erase(ii->first);
  }
  for (ActualCalleesTy::iterator ii = ActualCallees.begin(),
       ee = ActualCallees.end(); ii != ee; ++ii)
    removeECs(ii->second, SCCs);
}

void DSCallGraph::buildRoots() {
  FuncSet knownCallees;
  FuncSet knownCallers;
  for (SimpleCalleesTy::iterator ii = SimpleCallees.begin(),
       ee = SimpleCallees.end(); ii != ee; ++ii) {
    knownCallees.insert(ii->second.begin(), ii->second.end());
    knownCallers.insert(ii->first);
  }
  knownRoots.clear();
  std::set_difference(knownCallers.begin(), knownCallers.end(),
                      knownCallees.begin(), knownCallees.end(),
                     std::inserter(knownRoots, knownRoots.begin()));
}

void DSCallGraph::buildIncompleteCalleeSet(svset<const llvm::Function*> callees) {
  IncompleteCalleeSet.insert(callees.begin(), callees.end());
}

template <class T>
void printNameOrPtr(T& Out, const llvm::Function* F) {
  if (F->hasName())
    Out << F->getName();
  else
    Out << F;
}

void DSCallGraph::dump() {
  //function map

  //CallGraph map
  for (SimpleCalleesTy::iterator ii = SimpleCallees.begin(),
       ee = SimpleCallees.end(); ii != ee; ++ii) {
    llvm::errs() << "CallGraph[";
    printNameOrPtr(llvm::errs(), ii->first);
    llvm::errs() << "]";
    for (FuncSet::iterator i = ii->second.begin(),
         e = ii->second.end(); i != e; ++i) {
      llvm::errs() << " ";
      printNameOrPtr(llvm::errs(), *i);
    }
    llvm::errs() << "\n";
  }

  //Functions we know about that aren't called
  llvm::errs() << "Roots:";
  for (FuncSet::iterator ii = knownRoots.begin(), ee = knownRoots.end();
       ii != ee; ++ii) {
    llvm::errs() << " ";
    printNameOrPtr(llvm::errs(), *ii);
  }
  llvm::errs() << "\n";
}

//
// Method: insert()
//
// Description:
//  Insert a new entry into the call graph.  This entry says that the specified
//  call site calls the specified function.
//
// Inputs:
//  CS - The call site which calls the specified function.
//  F  - The function which is called.  This is permitted to be NULL.  It is
//       possible to have call sites that don't have any targets, and sometimes
//       users just want to ensure that a call site has an entry within the
//       call graph.
//
void
DSCallGraph::insert(llvm::CallSite CS, const llvm::Function* F) {
  //
  // Find the function to which the call site belongs.
  //
  const llvm::Function * Parent = CS.getInstruction()->getParent()->getParent();

  //
  // Determine the SCC leaders for both the calling function and the called
  // function.  If they don't belong to an SCC, add them as leaders.
  //
  SCCs.insert (Parent);
  SCCs.insert (F);
  const llvm::Function * ParentLeader = SCCs.getLeaderValue (Parent);
  const llvm::Function * FLeader      = SCCs.getLeaderValue (F);

  //
  // Create an empty set for the callee; hence, all called functions get to be
  // in the call graph also.  This simplifies SCC formation.
  //
  SimpleCallees[ParentLeader];
  if (F) {
    ActualCallees[CS].insert(FLeader);
    SimpleCallees[ParentLeader].insert(FLeader);
  }
}

void DSCallGraph::insureEntry(const llvm::Function* F) {
  SimpleCallees[F];
}

void DSCallGraph::addFullFunctionSet(llvm::CallSite CS,
                    svset<const llvm::Function*> &Set) const {
  DSCallGraph::callee_iterator csi = callee_begin(CS),
                               cse = callee_end(CS);
  while(csi != cse) {
    const Function *F = *csi;
    Set.insert(scc_begin(F), scc_end(F));
    ++csi;
  }
  const Function *F1 = CS.getInstruction()->getParent()->getParent();
  F1 = sccLeader(&*F1);
  Set.insert(scc_begin(F1), scc_end(F1));
}
