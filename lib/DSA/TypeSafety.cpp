//===- TypeSafety.cpp - Find type-safe pointers --------------------------- --//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// This pass implements code that determines if memory objects are used in
// a type-consistent fashion.  It is built using DSA and essentially abstracts
// away the details of interpreting DSNodes.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "type-safety"

#include "dsa/TypeSafety.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/Statistic.h"

static RegisterPass<dsa::TypeSafety<EQTDDataStructures> >
X ("typesafety-eqtd", "Find type-safe pointers");
static RegisterPass<dsa::TypeSafety<TDDataStructures> >
Y ("typesafety-td", "Find type-safe pointers");

// Pass Statistics
namespace {
  //STATISTIC (TypeSafeNodes, "Type-safe DSNodes");
}
extern cl::opt<bool> TypeInferenceOptimize;

namespace dsa {

template<typename dsa>
char TypeSafety<dsa>::ID = 0;

// Method: getDSNodeHandle()
//
// Description:
//  This method looks up the DSNodeHandle for a given LLVM globalvalue. 
//  The value is looked up in the globals graph
//
// Return value:
//  A DSNodeHandle for the value is returned.  This DSNodeHandle is from 
//  the GlobalsGraph.  Note that the DSNodeHandle may represent a NULL DSNode.
//
template<class dsa> DSNodeHandle
TypeSafety<dsa>::getDSNodeHandle(const GlobalValue *V) {
  DSNodeHandle DSH;
  const DSGraph * GlobalsGraph = dsaPass->getGlobalsGraph ();
  if(GlobalsGraph->hasNodeForValue(V)) {
    DSH = GlobalsGraph->getNodeForValue(V);
  }
  //
  // Try looking up this DSNode value in the globals graph.  Note that
  // globals are put into equivalence classes; we may need to first find the
  // equivalence class to which our global belongs, find the global that
  // represents all globals in that equivalence class, and then look up the
  // DSNode Handle for *that* global.
  //
  if (DSH.isNull()) {
    //
    // DSA does not currently handle global aliases.
    //
    if (!isa<GlobalAlias>(V)) {
      //
      // We have to dig into the globalEC of the DSGraph to find the DSNode.
      //
      const GlobalValue * GV = dyn_cast<GlobalValue>(V);
      const GlobalValue * Leader;
      Leader = GlobalsGraph->getGlobalECs().getLeaderValue(GV);
      DSH = GlobalsGraph->getNodeForValue(Leader);
    }
  }
  return DSH;
}

// Method: getDSNodeHandle()
//
// Description:
//  This method looks up the DSNodeHandle for a given LLVM value.  The context
//  of the value is the specified function, although if it is a global value,
//  the DSNodeHandle may exist within the global DSGraph.
//
// Return value:
//  A DSNodeHandle for the value is returned.  This DSNodeHandle could either
//  be in the function's DSGraph or from the GlobalsGraph.  Note that the
//  DSNodeHandle may represent a NULL DSNode.
//
template<class dsa> DSNodeHandle
TypeSafety<dsa>::getDSNodeHandle (const Value * V, const Function * F) {
  //
  // Ensure that the function has a DSGraph
  //
  assert (dsaPass->hasDSGraph(*F) && "No DSGraph for function!\n");

  //
  // Lookup the DSNode for the value in the function's DSGraph.
  //
  const DSGraph * TDG = dsaPass->getDSGraph(*F);

  DSNodeHandle DSH;
  if(TDG->hasNodeForValue(V))
    DSH = TDG->getNodeForValue(V);

  //
  // If the value wasn't found in the function's DSGraph, then maybe we can
  // find the value in the globals graph.
  //
  if ((DSH.isNull()) && (isa<GlobalValue>(V))) {
    //
    // Try looking up this DSNode value in the globals graph.  Note that
    // globals are put into equivalence classes; we may need to first find the
    // equivalence class to which our global belongs, find the global that
    // represents all globals in that equivalence class, and then look up the
    // DSNode Handle for *that* global.
    //
    DSH = getDSNodeHandle(cast<GlobalValue>(V));
  }
  return DSH;
}

template<class dsa> bool
TypeSafety<dsa>::isTypeSafe (const Value * V, const Function * F) {
  //
  // Get the DSNode for the specified value.
  //
  DSNodeHandle DH = getDSNodeHandle (V, F);

  //
  // If there is no DSNode, claim that it is not type safe.
  //
  if (DH.isNull()) {
    return false;
  }

  //
  // See if the DSNode is one that we think is type-safe.
  //
  if (TypeSafeNodes.count (DH.getNode()))
    return true;

  return false;
}

template<class dsa> bool
TypeSafety<dsa>::isTypeSafe(const GlobalValue *V) {
  //
  // Get the DSNode for the specified value.
  //
  DSNodeHandle DH = getDSNodeHandle(V);

  //
  // If there is no DSNode, claim that it is not typesafe.
  //
  if (DH.isNull())
    return false;

  //
  // See if the DSNode is one that we think is type-safe.
  //
  if (TypeSafeNodes.count (DH.getNode()))
    return true;

  return false;
}

//
// Method: typeFieldsOverlap()
//
// Description:
//  Determine if any of the type fields can overlap within the DSNode.
//
// Notes:
//  o) We take advantage of the fact that a std::map keeps its elements sorted
//     by key.
//
template<class dsa> bool
TypeSafety<dsa>::typeFieldsOverlap (const DSNode * N) {
  //
  // There are no overlapping fields if the DSNode has no fields.
  //
  if (N->type_begin() == N->type_end())
    return false;

  //
  // Iterate through the DSNode to see if the previous fields overlaps with the
  // current field.
  //
  DSNode::const_type_iterator tn =  N->type_begin();
  bool overlaps = false;
  while (!overlaps) {
    //
    // Get the information about the current field.
    //
    unsigned offset = tn->first;
    SuperSet<Type*>::setPtr TypeSet = tn->second;

    //
    // If this is the last field, then we are done searching.
    //
    if ((++tn) == N->type_end()) {
      break;
    }

    //
    // Get the offset of the next field.
    //
    unsigned next_offset = tn->first;

    //
    // Check to see if any of the types in the current field extend into the
    // next field.
    //
    if (TypeSet) {
      for (svset<Type*>::const_iterator ni = TypeSet->begin(),
           ne = TypeSet->end(); ni != ne; ++ni) {
        unsigned field_length = TD->getTypeStoreSize (*ni);
        if ((offset + field_length) > next_offset) {
          overlaps = true;
          if(TypeInferenceOptimize) {
            if(const ArrayType *AT = dyn_cast<ArrayType>(*ni)) {
              Type *ElemTy = AT->getElementType();
              while(ArrayType *AT1 = dyn_cast<ArrayType>(ElemTy))
                ElemTy = AT1->getElementType();
              if(next_offset < (TD->getTypeStoreSize(ElemTy) + offset)) {
                assert(isa<StructType>(ElemTy) && "Array Not of Struct Type??");
                overlaps = false;
              }
            }
          }
          if(overlaps) {
            DEBUG(errs() << " Found overlap at " << offset << " with " << next_offset << "\n");
            break;
          }
        }
      }
    }
  }

  //
  // Return the result.
  //
  return overlaps;
}

//
// Method: isTypeSafe()
//
// Description:
//  Determine whether a DSNode represents a piece of memory that is accessed
//  in a type-safe fasion.
//
// Inputs:
//  N - A pointer to a DSNode representing the memory object.
//
// Return value:
//  true  - The memory object is used in a type-safe fasion.
//  false - The memory object *may* be used in a type-unsafe fasion.
//
template<class dsa> bool
TypeSafety<dsa>::isTypeSafe (const DSNode * N) {
  //
  // If the DSNode is completely folded, then we know for sure that it is not
  // type-safe.
  //
  if (N->isNodeCompletelyFolded())
    return false;

  //
  // If the memory object represented by this DSNode can be manipulated by
  // external code or DSA has otherwise not finished analyzing all operations
  // on it, declare it type-unsafe.
  //
  if (N->isExternalNode() || N->isIncompleteNode())
    return false;

  //
  // If the pointer to the memory object came from some source not understood
  // by DSA or somehow came from/escapes to the realm of integers, declare it
  // type-unsafe.
  //
  if (N->isUnknownNode() || N->isIntToPtrNode() || N->isPtrToIntNode()) {
    return false;
  }

  //
  // Scan through all of the fields within the DSNode and see if any overlap.
  // If they do, then the DSNode is not type-safe.
  //
  if (typeFieldsOverlap (N))
    return false;

  //
  // We have run out of reasons for this DSNode to be type-unsafe.  Declare it
  // type-safe.
  //
  return true;
}

//
// Method: findTypeSafeDSNodes()
//
// Description:
//  Find and record all type-safe DSNodes.
//
// Inputs:
//  Graph - The DSGraph for which we should search for type-safe nodes.
//
// Side-effects:
//  Class level data structures are updated to record which DSNodes are
//  type-safe.
//
template<class dsa> void
TypeSafety<dsa>::findTypeSafeDSNodes (const DSGraph * Graph) {
  DSGraph::node_const_iterator N = Graph->node_begin();
  DSGraph::node_const_iterator NE = Graph->node_end();
  for (; N != NE; ++N) {
    if (isTypeSafe (N)) {
      TypeSafeNodes.insert (&*N);
    }
  }
}

template<class dsa> bool
TypeSafety<dsa>::runOnModule(Module & M) {
  //
  // Get access to prerequisite passes.
  //
  TD      = &getAnalysis<DataLayoutPass>().getDataLayout();
  dsaPass = &getAnalysis<dsa>();

  //
  // For every DSGraph, find which DSNodes are type-safe.
  //
  findTypeSafeDSNodes (dsaPass->getGlobalsGraph());
  for (Module::iterator F = M.begin(); F != M.end(); ++F) {
    if (dsaPass->hasDSGraph (*F)) {
      findTypeSafeDSNodes (dsaPass->getDSGraph (*F));
    }
  }

  return false;
}

}

