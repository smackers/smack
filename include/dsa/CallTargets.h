//=- llvm/Analysis/CallTargets.h - Resolve Indirect Call Targets --*- C++ -*-=//
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
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_CALLTARGETS_H
#define LLVM_ANALYSIS_CALLTARGETS_H

#include "llvm/Pass.h"
#include "llvm/IR/CallSite.h"
#include "dsa/DataStructure.h"

#include <set>
#include <list>
#include <map>

using namespace llvm;
namespace dsa{

  template<class dsa>
  class CallTargetFinder : public ModulePass {
    std::map<CallSite, std::vector<const Function*> > IndMap;
    std::set<CallSite> CompleteSites;
    std::list<CallSite> AllSites;

    void findIndTargets(Module &M);
  public:
    static char ID;
    CallTargetFinder() : ModulePass(ID) {}

    virtual bool runOnModule(Module &M);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const;

    virtual void print(llvm::raw_ostream &O, const Module *M) const;

    // Given a CallSite, get an iterator of callees
    std::vector<const Function*>::iterator begin(CallSite cs){
      return IndMap[cs].begin();
    }
    std::vector<const Function*>::iterator end(CallSite cs){
      return IndMap[cs].end();
    }
    unsigned size(CallSite cs){
      return IndMap[cs].size();
    }

    // Iterate over CallSites in program
    std::list<CallSite>::iterator cs_begin(){
      return AllSites.begin();
    }
    std::list<CallSite>::iterator cs_end(){
      return AllSites.end();
    }

    // Do we think we have complete knowledge of this site?
    // That is, do we think there are no missing callees
    bool isComplete(CallSite cs) const {
      return CompleteSites.find(cs) != CompleteSites.end();
    }
  };
  
}

#endif
