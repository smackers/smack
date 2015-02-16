//===- TypeSafety.h - Find Type-Safe Pointers ---------------------*- C++ -*--//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// This analysis pass determines which pointers within a program are used in
// a type-safe fashion.  It uses DSA to determine type-consistency and
// abstracts the details of interpreting DSA's results.
//
//===----------------------------------------------------------------------===//

#ifndef DSA_TYPESAFETY_H
#define DSA_TYPESAFETY_H

#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"

#include "llvm/Pass.h"

#include <set>

using namespace llvm;

namespace dsa {

//
// Pass: TypeSafety
//
// Description:
//  This pass determines which pointers within a function are type-safe.  It is
//  used to abstract away the interpretation of the DSNode flags and fields
//  for clients.
//
// Template parameters:
//  dsa - The name of the DSA Pass which this pass should use.
//
template<class dsa>
struct TypeSafety : public ModulePass {
  protected:
    // Methods
    DSNodeHandle getDSNodeHandle (const Value * V, const Function * F);
    DSNodeHandle getDSNodeHandle (const GlobalValue * V);
    void findTypeSafeDSNodes (const DSGraph * Graph);
    bool isTypeSafe (const DSNode * N);
    bool typeFieldsOverlap (const DSNode * N);

    // Pointers to prerequisite passes
    const DataLayout * TD;
    dsa * dsaPass;

    // Data structures
    std::set<const DSNode *> TypeSafeNodes;

  public:
    static char ID;
    TypeSafety() : ModulePass(ID) {}
    virtual bool runOnModule (Module & M);

    const char *getPassName() const {
      return "DSA Type-Safety Analysis";
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<DataLayoutPass>();
      AU.addRequired<dsa>();
      AU.setPreservesAll();
    }

    virtual void releaseMemory () {
      TypeSafeNodes.clear();
      return;
    }

    // Methods for clients to use
    virtual bool isTypeSafe (const Value * V, const Function * F);
    virtual bool isTypeSafe (const GlobalValue * V);
};

}
#endif

