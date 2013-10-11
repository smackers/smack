//===- DSNode.h - Node definition for datastructure graphs ------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Data structure graph nodes and some implementation of DSNodeHandle.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_DSNODE_H
#define LLVM_ANALYSIS_DSNODE_H

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ilist_node.h"
#include "llvm/ADT/ilist.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "dsa/svset.h"
#include "dsa/super_set.h"
#include "dsa/keyiterator.h"
#include "dsa/DSGraph.h"
#include "dsa/DSSupport.h"

#include <map>
#include <set>

namespace llvm {

template<typename BaseType>
class DSNodeIterator;          // Data structure graph traversal iterator

//===----------------------------------------------------------------------===//
/// DSNode - Data structure node class
///
/// This class represents an untyped memory object of Size bytes.  It keeps
/// track of any pointers that have been stored into the object as well as the
/// different types represented in this object.
///
class DSNode : public ilist_node<DSNode> {
public:
  typedef std::map<unsigned, SuperSet<Type*>::setPtr> TyMapTy;
  typedef std::map<unsigned, DSNodeHandle> LinkMapTy;

private:
  friend struct ilist_sentinel_traits<DSNode>;
  //Sentinel
  DSNode() : NumReferrers(0), Size(0), NodeType(0) {}
  
  /// NumReferrers - The number of DSNodeHandles pointing to this node... if
  /// this is a forwarding node, then this is the number of node handles which
  /// are still forwarding over us.
  ///
  unsigned NumReferrers;

  /// ForwardNH - This NodeHandle contain the node (and offset into the node)
  /// that this node really is.  When nodes get folded together, the node to be
  /// eliminated has these fields filled in, otherwise ForwardNH.getNode() is
  /// null.
  ///
  DSNodeHandle ForwardNH;

  /// Size - The current size of the node.  This should be equal to the size of
  /// the current type record.
  ///
  unsigned Size;

  /// ParentGraph - The graph this node is currently embedded into.
  ///
  DSGraph *ParentGraph;

  /// TyMap - Keep track of the loadable types and offsets those types are seen
  // at.
  TyMapTy TyMap;

  /// Links - Contains one entry for every byte in this memory
  /// object.  
  ///
  LinkMapTy Links;

  /// Globals - The list of global values that are merged into this node.
  ///
  svset<const GlobalValue*> Globals;

  void operator=(const DSNode &); // DO NOT IMPLEMENT
  DSNode(const DSNode &);         // DO NOT IMPLEMENT
public:
  enum NodeTy {
    ShadowNode      = 0,        // Nothing is known about this node...
    AllocaNode      = 1 << 0,   // This node was allocated with alloca
    HeapNode        = 1 << 1,   // This node was allocated with malloc
    GlobalNode      = 1 << 2,   // This node was allocated by a global var decl
    ExternFuncNode  = 1 << 3,   // This node contains external functions
    ExternGlobalNode = 1 << 4,  // This node contains external globals
    UnknownNode     = 1 << 5,   // This node points to unknown allocated memory
    IncompleteNode  = 1 << 6,   // This node may not be complete

    ModifiedNode    = 1 << 7,   // This node is modified in this context
    ReadNode        = 1 << 8,   // This node is read in this context

    ArrayNode       = 1 << 9,   // This node is treated like an array
    CollapsedNode   = 1 << 10,  // This node is collapsed
    ExternalNode    = 1 << 11,  // This node comes from an external source
    IntToPtrNode    = 1 << 12,  // This node comes from an int cast
                                // and is used in pointer operations
                                // like geps, loads, stores
    PtrToIntNode    = 1 << 13,  // This node escapes to an int cast 
                                // and DSA does not track it further.
    VAStartNode     = 1 << 14,  // This node is from a vastart call

    //#ifndef NDEBUG
    DeadNode        = 1 << 15,   // This node is dead and should not be pointed to
    //#endif

    Composition = AllocaNode | HeapNode | GlobalNode | UnknownNode
  };

  /// NodeType - A union of the above bits.  "Shadow" nodes do not add any flags
  /// to the nodes in the data structure graph, so it is possible to have nodes
  /// with a value of 0 for their NodeType.
  ///
private:
  unsigned short NodeType;
public:

  /// DSNode ctor - Create a node of the specified type, inserting it into the
  /// specified graph.
  ///
  explicit DSNode(DSGraph *G);

  /// DSNode "copy ctor" - Copy the specified node, inserting it into the
  /// specified graph.  If NullLinks is true, then null out all of the links,
  /// but keep the same number of them.  This can be used for efficiency if the
  /// links are just going to be clobbered anyway.
  ///
  DSNode(const DSNode &, DSGraph *G, bool NullLinks = false);
  ~DSNode();

  // Iterator for graph interface... Defined in DSGraphTraits.h
  typedef DSNodeIterator<DSNode> iterator;
  typedef DSNodeIterator<const DSNode> const_iterator;
  inline iterator begin();
  inline iterator end();
  inline const_iterator begin() const;
  inline const_iterator end() const;

  /// type_* - Provide iterators for accessing types.  Some types may be null
  typedef TyMapTy::iterator type_iterator;
  typedef TyMapTy::const_iterator const_type_iterator;
  type_iterator type_begin() { return TyMap.begin(); }
  type_iterator type_end()   { return TyMap.end(); }
  const_type_iterator type_begin() const { return TyMap.begin(); }
  const_type_iterator type_end()   const { return TyMap.end(); }

  /// edge_* - Provide iterators for accessing outgoing edges.  Some outgoing
  /// edges may be null.
  typedef LinkMapTy::iterator edge_iterator;
  typedef LinkMapTy::const_iterator const_edge_iterator;
  edge_iterator edge_begin() { return Links.begin(); }
  edge_iterator edge_end() { return Links.end(); }
  const_edge_iterator edge_begin() const { return Links.begin(); }
  const_edge_iterator edge_end() const { return Links.end(); }

  //===--------------------------------------------------
  // Accessors

  /// getSize - Return the maximum number of bytes occupied by this object...
  ///
  unsigned getSize() const { return Size; }

  /// hasNoReferrers - Return true if nothing is pointing to this node at all.
  ///
  bool hasNoReferrers() const { return getNumReferrers() == 0; }

  /// getNumReferrers - This method returns the number of referrers to the
  /// current node.  Note that if this node is a forwarding node, this will
  /// return the number of nodes forwarding over the node!
  unsigned getNumReferrers() const { return NumReferrers; }


  DSGraph *getParentGraph() const { return ParentGraph; }
  void setParentGraph(DSGraph *G) { ParentGraph = G; }

  /// getForwardNode - This method returns the node that this node is forwarded
  /// to, if any.
  ///
  DSNode *getForwardNode() const { return ForwardNH.getNode(); }

  /// isForwarding - Return true if this node is forwarding to another.
  ///
  bool isForwarding() const { return !ForwardNH.isNull(); }

  /// stopForwarding - When the last reference to this forwarding node has been
  /// dropped, delete the node.
  ///
  void stopForwarding() {
    assert(isForwarding() &&
           "Node isn't forwarding, cannot stopForwarding()!");
    ForwardNH.setTo(0, 0);
    assert(ParentGraph == 0 &&
           "Forwarding nodes must have been removed from graph!");
    delete this;
  }

  void growSize(unsigned NSize) {
    assert(NSize >= Size && "Cannot shrink");
    assert(!isCollapsedNode() && "Growing a collapsed node");
    Size = NSize;
  }
  
  void growSizeForType(Type *Ty, unsigned Offset);

  /// hasLink - Return true if this memory object has a link in slot LinkNo
  ///
  bool hasLink(unsigned Offset) const {
    assert(Offset < getSize() && "Link index is out of range!");
    return Links.find(Offset) != Links.end();
  }

  /// getLink - Return the link at the specified offset.
  ///
  DSNodeHandle &getLink(unsigned Offset) {
    assert(Offset < getSize() && "Link index is out of range!");
    assert(!isForwarding() && "Link on a forwarding node");
    return Links[Offset];
   }
  const DSNodeHandle &getLink(unsigned Offset) const {
    assert(hasLink(Offset) && "No Link");
    assert(!isForwarding() && "Link on a forwarding node");
    return Links.find(Offset)->second;
  }

  //unsigned getNumLinks() const {
//     assert(!isForwarding() && "Link on a forwarding node");
//    return Links.size();
//  }

  /// mergeTypeInfo - This method merges the specified type into the current
  /// node at the specified offset.  This may update the current node's type
  /// record if this gives more information to the node, it may do nothing to
  /// the node if this information is already known, or it may merge the node
  /// completely (and return true) if the information is incompatible with what
  /// is already known.
  ///
  void mergeTypeInfo(Type *Ty, unsigned Offset);
  void mergeTypeInfo(const TyMapTy::mapped_type TyIt, unsigned Offset);
  void mergeTypeInfo(const DSNode* D, unsigned Offset);

  // Types records might exist without types in them
  bool hasNoType() {
    type_iterator ii = type_begin(), ee = type_end();
    while (ii != ee) {
      if (ii->second) return false;
      ++ii;
    }
    return true;
  }

  /// markIntPtrFlags - If the node at any offset has overlapping int/ptr types
  /// mark the P2I flags.
  ///
  void markIntPtrFlags();

  /// foldNodeCompletely - If we determine that this node has some funny
  /// behavior happening to it that we cannot represent, we fold it down to a
  /// single, completely pessimistic, node.  This node is represented as a
  /// single byte with a single TypeEntry of "void" with isArray = true.
  ///
  void foldNodeCompletely();

  /// isNodeCompletelyFolded - Return true if this node has been completely
  /// folded down to something that can never be expanded, effectively losing
  /// all of the field sensitivity that may be present in the node.
  ///
  bool isNodeCompletelyFolded() const;

  /// setLink - Set the link at the specified offset to the specified
  /// NodeHandle, replacing what was there.  It is uncommon to use this method,
  /// instead one of the higher level methods should be used, below.
  ///
  void setLink(unsigned Offset, const DSNodeHandle &NH) {
    assert(Offset < getSize() && "Link index is out of range!");
    Links[Offset] = NH;
  }

  /// addEdgeTo - Add an edge from the current node to the specified node.  This
  /// can cause merging of nodes in the graph.
  ///
  void addEdgeTo(unsigned Offset, const DSNodeHandle &NH);

  /// mergeWith - Merge this node and the specified node, moving all links to
  /// and from the argument node into the current node, deleting the node
  /// argument.  Offset indicates what offset the specified node is to be merged
  /// into the current node.
  ///
  /// The specified node may be a null pointer (in which case, nothing happens).
  ///
  void mergeWith(const DSNodeHandle &NH, unsigned Offset);

  /// addGlobal - Add an entry for a global value to the Globals list.  This
  /// also marks the node with the 'G' flag if it does not already have it.
  ///
  void addGlobal(const GlobalValue *GV);

  void addFunction(const Function* F);

  /// removeGlobal - Remove the specified global that is explicitly in the
  /// globals list.
  void removeGlobal(const GlobalValue *GV);

  void mergeGlobals(const DSNode& RHS);
  void clearGlobals() { Globals.clear(); }

  bool isEmptyGlobals() const { return Globals.empty(); }
  unsigned numGlobals() const { return Globals.size(); }

  /// addFullGlobalSet - Compute the full set of global values that are
  /// represented by this node.  Unlike getGlobalsList(), this requires fair
  /// amount of work to compute, so don't treat this method call as free.
  void addFullGlobalsSet(svset<const GlobalValue*> &Set) const;
  /// Same as above, keeping for compat reasons
  void addFullGlobalsList(std::vector<const GlobalValue*> &List) const {
    svset<const GlobalValue*> Set;
    addFullGlobalsSet(Set);
    List.insert(List.end(), Set.begin(), Set.end());
  }

  /// addFullFunctionSet - Identical to addFullGlobalsSet, but only return the
  /// functions in the full list.
  void addFullFunctionSet(svset<const Function*> &Set) const;
  /// Same as above, keeping for compat reasons
  void addFullFunctionList(std::vector<const Function*> &List) const {
    svset<const Function*> Set;
    addFullFunctionSet(Set);
    List.insert(List.end(), Set.begin(), Set.end());
  }
  /// Same as above, only doesn't include duplicates
  /// (keeping both for compat with existing clients)

  /// globals_iterator/begin/end - Provide iteration methods over the global
  /// value leaders set that is merged into this node.  Like the getGlobalsList
  /// method, these iterators do not return globals that are part of the
  /// equivalence classes for globals in this node, but aren't leaders.
  typedef svset<const GlobalValue*>::const_iterator globals_iterator;
  globals_iterator globals_begin() const { return Globals.begin(); }
  globals_iterator globals_end() const { return Globals.end(); }

  /// addValueList - Compute a full set of values that are represented by
  /// this node. High overhead method.
  void addValueList(std::vector<const Value*> &List) const;

  /// maskNodeTypes - Apply a mask to the node types bitfield.
  ///
  void maskNodeTypes(unsigned Mask) {
    NodeType &= Mask;
  }

  void mergeNodeFlags(unsigned RHS) {
    NodeType |= RHS;
  }

  /// getNodeFlags - Return all of the flags set on the node.  If the DEAD flag
  /// is set, hide it from the caller.
  ///
  unsigned getNodeFlags() const { return NodeType & ~DeadNode; }

  /// clearNodeFlags - Useful for completely resetting a node, 
  /// used in external recognizers
  DSNode* clearNodeFlags() { NodeType = 0; return this; }

  bool isAllocaNode()     const { return NodeType & AllocaNode;    }
  bool isHeapNode()       const { return NodeType & HeapNode;      }
  bool isGlobalNode()     const { return NodeType & GlobalNode;    }
  bool isExternFuncNode() const { return NodeType & ExternFuncNode; }
  bool isUnknownNode()    const { return NodeType & UnknownNode;   }
  bool isModifiedNode()   const { return NodeType & ModifiedNode;  }
  bool isReadNode()       const { return NodeType & ReadNode;      }
  bool isArrayNode()      const { return NodeType & ArrayNode;     }
  bool isCollapsedNode()  const { return NodeType & CollapsedNode; }
  bool isIncompleteNode() const { return NodeType & IncompleteNode;}
  bool isCompleteNode()   const { return !isIncompleteNode();      }
  bool isDeadNode()       const { return NodeType & DeadNode;      }
  bool isExternalNode()   const { return NodeType & ExternalNode;  }
  bool isIntToPtrNode()   const { return NodeType & IntToPtrNode;  }
  bool isPtrToIntNode()   const { return NodeType & PtrToIntNode;  }
  bool isVAStartNode()    const { return NodeType & VAStartNode;   }

  DSNode* setAllocaMarker()     { NodeType |= AllocaNode;     return this; }
  DSNode* setHeapMarker()       { NodeType |= HeapNode;       return this; }
  DSNode* setGlobalMarker()     { NodeType |= GlobalNode;     return this; }
  DSNode* setExternFuncMarker() { NodeType |= ExternFuncNode; return this; }
  DSNode* setExternGlobalMarker() { NodeType |= ExternGlobalNode; return this; }
  DSNode* setUnknownMarker()    { NodeType |= UnknownNode;    return this; }
  DSNode* setModifiedMarker()   { NodeType |= ModifiedNode;   return this; }
  DSNode* setReadMarker()       { NodeType |= ReadNode;       return this; }
  DSNode* setArrayMarker()      { NodeType |= ArrayNode;      return this; }
  DSNode* setCollapsedMarker()  { NodeType |= CollapsedNode;  return this; }
  DSNode* setIncompleteMarker() { NodeType |= IncompleteNode; return this; }
  DSNode* setExternalMarker()   { NodeType |= ExternalNode;   return this; }
  DSNode* setIntToPtrMarker()   { NodeType |= IntToPtrNode;   return this; }
  DSNode* setPtrToIntMarker()   { NodeType |= PtrToIntNode;   return this; }
  DSNode* setVAStartMarker()    { NodeType |= VAStartNode;    return this; }

  void makeNodeDead() {
    Globals.clear();
    assert(hasNoReferrers() && "Dead node shouldn't have refs!");
    NodeType = DeadNode;
  }

  /// forwardNode - Mark this node as being obsolete, and all references to it
  /// should be forwarded to the specified node and offset.
  ///
  void forwardNode(DSNode *To, unsigned Offset);

  void cleanEdges();

  void print(llvm::raw_ostream &O, const DSGraph *G) const;
  void dump() const;
  void dumpParentGraph() const;
  void dumpFuncs();

  void assertOK() const;

  void dropAllReferences() {
    Links.clear();
    TyMap.clear();
    if (isForwarding())
      ForwardNH.setTo(0, 0);
  }

  /// remapLinks - Change all of the Links in the current node according to the
  /// specified mapping.
  ///
  void remapLinks(std::map<const DSNode*, DSNodeHandle> &OldNodeMap);

  /// markReachableNodes - This method recursively traverses the specified
  /// DSNodes, marking any nodes which are reachable.  All reachable nodes it
  /// adds to the set, which allows it to only traverse visited nodes once.
  ///
  void markReachableNodes(llvm::DenseSet<const DSNode*> &ReachableNodes) const;


  /// checkOffsetFoldIfNeeded - Fold DSNode if the specified offset is
  /// larger than its size, and the node isn't an array or forwarding.
  void checkOffsetFoldIfNeeded(int Offset);
private:
  friend class DSNodeHandle;

  // static mergeNodes - Helper for mergeWith()
  static void MergeNodes(DSNodeHandle& CurNodeH, DSNodeHandle& NH);
};

//===----------------------------------------------------------------------===//
// Define inline DSNodeHandle functions that depend on the definition of DSNode
//
inline DSNode *DSNodeHandle::getNode() const {
  // Disabling this assertion because it is failing on a "magic" struct
  // in named (from bind).  The fourth field is an array of length 0,
  // presumably used to create struct instances of different sizes.
  // In a variable length struct, Offset could exceed Size when getNode()
  // is called before such a node is folded. In this case, the DS Analysis now 
  // correctly folds this node after calling getNode.
  /*  assert((!N ||
          N->isNodeCompletelyFolded() ||
          (N->Size == 0 && Offset == 0) ||
          (int(Offset) >= 0 && Offset < N->Size) ||
          (int(Offset) < 0 && -int(Offset) < int(N->Size)) ||
          N->isForwarding()) && "Node handle offset out of range!");
  */
  if (N == 0 || !N->isForwarding())
    return N;

  return HandleForwarding();
}

inline void DSNodeHandle::setTo(DSNode *n, unsigned NewOffset) const {
  assert((!n || !n->isForwarding()) && "Cannot set node to a forwarded node!");
  if (N) getNode()->NumReferrers--;
  N = n;
  Offset = NewOffset;
  if (N) {
    N->NumReferrers++;
    if (Offset >= N->Size) {
      assert((Offset == 0 || N->Size == 1) &&
             "Pointer to non-collapsed node with invalid offset!");
      Offset = 0;
    }
  }
  assert(!N || ((N->NodeType & DSNode::DeadNode) == 0));
  assert((!N || Offset < N->Size || (N->Size == 0 && Offset == 0) ||
          N->isForwarding()) && "Node handle offset out of range!");
}

inline bool DSNodeHandle::hasLink(unsigned Num) const {
  assert(N && "DSNodeHandle does not point to a node yet!");
  return getNode()->hasLink(Num+Offset);
}


/// getLink - Treat this current node pointer as a pointer to a structure of
/// some sort.  This method will return the pointer a mem[this+Num]
///
inline const DSNodeHandle &DSNodeHandle::getLink(unsigned Off) const {
  assert(N && "DSNodeHandle does not point to a node yet!");
  return getNode()->getLink(Offset+Off);
}
inline DSNodeHandle &DSNodeHandle::getLink(unsigned Off) {
  assert(N && "DSNodeHandle does not point to a node yet!");
  return getNode()->getLink(Off+Offset);
}

inline void DSNodeHandle::setLink(unsigned Off, const DSNodeHandle &NH) {
  assert(N && "DSNodeHandle does not point to a node yet!");
  getNode()->setLink(Off+Offset, NH);
}

/// addEdgeTo - Add an edge from the current node to the specified node.  This
/// can cause merging of nodes in the graph.
///
inline void DSNodeHandle::addEdgeTo(unsigned Off, const DSNodeHandle &NH) {
  assert(N && "DSNodeHandle does not point to a node yet!");
  getNode()->addEdgeTo(Off+Offset, NH);
}

/// mergeWith - Merge the logical node pointed to by 'this' with the node
/// pointed to by 'N'.
///
inline void DSNodeHandle::mergeWith(const DSNodeHandle &NH) const {
  if (!isNull())
    getNode()->mergeWith(NH, Offset);
  else {   // No node to merge with, so just point to Node
    Offset = 0;
    DSNode *N = NH.getNode();
    setTo(N, NH.getOffset());
  }
}

} // End llvm namespace

#endif
