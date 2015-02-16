//===- DSCallGaph.h - Build call graphs -------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Implement a detailed call graph for DSA.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_DSCALLGRAPH_H
#define	LLVM_DSCALLGRAPH_H

#include "dsa/svset.h"
#include "dsa/keyiterator.h"

#include <cstddef>
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/IR/CallSite.h"

#include <cassert>
#include <map>

class DSCallGraph {
public:
  typedef svset<const llvm::Function*> FuncSet;
  typedef std::map<llvm::CallSite, FuncSet> ActualCalleesTy;
  typedef std::map<const llvm::Function*, FuncSet> SimpleCalleesTy;

private:
  // ActualCallees contains CallSite -> set of Function mappings
  ActualCalleesTy ActualCallees;

  // SimpleCallees contains Function -> set of Functions mappings
  SimpleCalleesTy SimpleCallees;

  // These are used for returning empty sets when the caller has no callees
  FuncSet EmptyActual;
  FuncSet EmptySimple;

  // An equivalence class is exactly an SCC
  llvm::EquivalenceClasses<const llvm::Function*> SCCs;

  // Functions we know about that aren't called
  svset<const llvm::Function*> knownRoots;
  
  // Functions that might be called from an incomplete
  // unresolved call site.
  svset<const llvm::Function*> IncompleteCalleeSet;

  svset<llvm::CallSite> completeCS;

  // Types for SCC construction
  typedef std::map<const llvm::Function*, unsigned> TFMap;
  typedef std::vector<const llvm::Function*> TFStack;

  // Tarjan's SCC algorithm
  unsigned tarjan_rec(const llvm::Function* F, TFStack& Stack, unsigned &NextID,
                      TFMap& ValMap);

  void removeECFunctions();

public:

  DSCallGraph() {}

  typedef ActualCalleesTy::mapped_type::const_iterator callee_iterator;
  typedef KeyIterator<ActualCalleesTy::const_iterator> callee_key_iterator;
  typedef SimpleCalleesTy::mapped_type::const_iterator flat_iterator;
  typedef KeyIterator<SimpleCalleesTy::const_iterator> flat_key_iterator;
  typedef FuncSet::const_iterator                      root_iterator;
  typedef llvm::EquivalenceClasses<const llvm::Function*>::member_iterator scc_iterator;

  void insert(llvm::CallSite CS, const llvm::Function* F);

  void insureEntry(const llvm::Function* F);

  template<class Iterator>
  void insert(llvm::CallSite CS, Iterator _begin, Iterator _end) {
    for (; _begin != _end; ++_begin)
      insert(CS, *_begin);
  }

  callee_iterator callee_begin(llvm::CallSite CS) const {
    ActualCalleesTy::const_iterator ii = ActualCallees.find(CS);
    if (ii == ActualCallees.end())
      return EmptyActual.end();
    return ii->second.begin();
  }

  callee_iterator callee_end(llvm::CallSite CS) const {
    ActualCalleesTy::const_iterator ii = ActualCallees.find(CS);
    if (ii == ActualCallees.end())
      return EmptyActual.end();
    return ii->second.end();
  }

  callee_key_iterator key_begin() const {
    return callee_key_iterator(ActualCallees.begin());
  }

  callee_key_iterator key_end() const {
    return callee_key_iterator(ActualCallees.end());
  }

  flat_iterator flat_callee_begin(const llvm::Function* F) const {
    SimpleCalleesTy::const_iterator ii = SimpleCallees.find(F);
    if (ii == SimpleCallees.end())
      return EmptySimple.end();
    return ii->second.begin();
  }

  flat_iterator flat_callee_end(const llvm::Function* F) const {
    SimpleCalleesTy::const_iterator ii = SimpleCallees.find(F);
    if (ii == SimpleCallees.end())
      return EmptySimple.end();
    return ii->second.end();
  }

  flat_key_iterator flat_key_begin() const {
    return flat_key_iterator(SimpleCallees.begin());
  }

  flat_key_iterator flat_key_end() const {
    return flat_key_iterator(SimpleCallees.end());
  }

  root_iterator root_begin() const {
    return knownRoots.begin();
  }

  root_iterator root_end() const {
    return knownRoots.end();
  }

  scc_iterator scc_begin(const llvm::Function* F) const {
    assert(F == SCCs.getLeaderValue(F) && "Requested non-leader");
    return SCCs.member_begin(SCCs.findValue(F));
  }

  scc_iterator scc_end(const llvm::Function* F) const {
    assert(F == SCCs.getLeaderValue(F) && "Requested non-leader");
    return SCCs.member_end();
  }
  
  const llvm::Function* sccLeader(const llvm::Function*F) const {
    return SCCs.getLeaderValue(F);
  }
  unsigned callee_size(llvm::CallSite CS) const {
    ActualCalleesTy::const_iterator ii = ActualCallees.find(CS);
    if (ii == ActualCallees.end())
      return 0;
    return ii->second.size();
  }

  bool called_from_incomplete_site(const llvm::Function *F) const {
    return !(IncompleteCalleeSet.find(F) 
             == IncompleteCalleeSet.end()); 
  }
  void callee_mark_complete(llvm::CallSite CS) {
    completeCS.insert(CS);
  }

  bool callee_is_complete(llvm::CallSite CS) const {
    return completeCS.find(CS) != completeCS.end();
  }

  unsigned size() const {
    unsigned sum = 0;
    for (ActualCalleesTy::const_iterator ii = ActualCallees.begin(),
            ee = ActualCallees.end(); ii != ee; ++ii)
      sum += ii->second.size();
    return sum;
  }

  unsigned flat_size() const {
    return SimpleCallees.size();
  }

  void buildSCCs();

  void buildRoots();

  void buildIncompleteCalleeSet(svset<const llvm::Function*> callees);

  void addFullFunctionSet(llvm::CallSite CS, svset<const llvm::Function*> &Set) const;
  // Temporary compat wrapper
  void addFullFunctionList(llvm::CallSite CS, std::vector<const llvm::Function*> &List) const {
    svset<const llvm::Function*> Set;
    addFullFunctionSet(CS, Set);
    List.insert(List.end(), Set.begin(), Set.end());
  }

  void dump();

  void assertSCCRoot(const llvm::Function* F) {
    assert(F == SCCs.getLeaderValue(F) && "Not Leader?");
  }

  // common helper; no good reason for it to be here rather than elsewhere
  static bool hasPointers(const llvm::Function* F);
  static bool hasPointers(llvm::CallSite& CS);

};

#endif	/* LLVM_DSCALLGRAPH_H */

