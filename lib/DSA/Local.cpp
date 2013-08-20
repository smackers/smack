//===- Local.cpp - Compute a local data structure graph for a function ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Compute the local version of the data structure graph for a function.  The
// external interface to this file is the DSGraph constructor.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "dsa-local"

#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Constants.h"
#include "llvm/DataLayout.h"
#include "llvm/DerivedTypes.h"
#include "llvm/InlineAsm.h"
#include "llvm/Intrinsics.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/Support/Timer.h"
#include "llvm/Use.h"

#include <fstream>

// FIXME: This should eventually be a FunctionPass that is automatically
// aggregated into a Pass.
//
#include "llvm/Module.h"

using namespace llvm;

namespace {
STATISTIC(NumDirectCall,    "Number of direct calls added");
STATISTIC(NumIndirectCall,  "Number of indirect calls added");
STATISTIC(NumAsmCall,       "Number of asm calls collapsed/seen");
STATISTIC(NumIntrinsicCall, "Number of intrinsics called");
STATISTIC(NumBoringIntToPtr, "Number of inttoptr used only in cmp");
//STATISTIC(NumSimpleIntToPtr, "Number of inttoptr from ptrtoint");
STATISTIC(NumIgnoredInst,       "Number of instructions ignored");

RegisterPass<LocalDataStructures>
X("dsa-local", "Local Data Structure Analysis");

cl::opt<std::string> hasMagicSections("dsa-magic-sections",
        cl::desc("File with section to global mapping")); //, cl::ReallyHidden);
}
cl::opt<bool> TypeInferenceOptimize("enable-type-inference-opts",
                                    cl::desc("Enable Type Inference Optimizations added to DSA."),
                                    cl::Hidden,
                                    cl::init(false));

namespace {
  //===--------------------------------------------------------------------===//
  //  GraphBuilder Class
  //===--------------------------------------------------------------------===//
  //
  /// This class is the builder class that constructs the local data structure
  /// graph by performing a single pass over the function in question.
  ///
  class GraphBuilder : InstVisitor<GraphBuilder> {
    DSGraph &G;
    Function* FB;
    LocalDataStructures* DS;
    const DataLayout& TD;
    DSNode *VAArray;

    ////////////////////////////////////////////////////////////////////////////
    // Helper functions used to implement the visitation functions...

    void MergeConstantInitIntoNode(DSNodeHandle &NH, Type* Ty, Constant *C);

    /// createNode - Create a new DSNode, ensuring that it is properly added to
    /// the graph.
    ///
    DSNode *createNode() 
    {   
      DSNode* ret = new DSNode(&G);
      assert(ret->getParentGraph() && "No parent?");
      return ret;
    }

    /// setDestTo - Set the ScalarMap entry for the specified value to point to
    /// the specified destination.  If the Value already points to a node, make
    /// sure to merge the two destinations together.
    ///
    void setDestTo(Value &V, const DSNodeHandle &NH);

    /// getValueDest - Return the DSNode that the actual value points to.
    ///
    DSNodeHandle getValueDest(Value* V);

    /// getLink - This method is used to return the specified link in the
    /// specified node if one exists.  If a link does not already exist (it's
    /// null), then we create a new node, link it, then return it.
    ///
    DSNodeHandle &getLink(const DSNodeHandle &Node, unsigned Link = 0);

    ////////////////////////////////////////////////////////////////////////////
    // Visitor functions, used to handle each instruction type we encounter...
    friend class InstVisitor<GraphBuilder>;

    void visitAllocaInst(AllocaInst &AI)
    { setDestTo(AI, createNode()->setAllocaMarker()); }

    //the simple ones
    void visitPHINode(PHINode &PN);
    void visitSelectInst(SelectInst &SI);
    void visitLoadInst(LoadInst &LI);
    void visitStoreInst(StoreInst &SI);
    void visitAtomicCmpXchgInst(AtomicCmpXchgInst &I);
    void visitAtomicRMWInst(AtomicRMWInst &I);
    void visitReturnInst(ReturnInst &RI);
    void visitVAArgInst(VAArgInst   &I);
    void visitIntToPtrInst(IntToPtrInst &I);
    void visitPtrToIntInst(PtrToIntInst &I);
    void visitBitCastInst(BitCastInst &I);
    void visitCmpInst(CmpInst &I);
    void visitInsertValueInst(InsertValueInst& I);
    void visitExtractValueInst(ExtractValueInst& I);

    //the nasty ones
    void visitGetElementPtrInst(User &GEP);
    void visitCallInst(CallInst &CI);
    void visitInvokeInst(InvokeInst &II);
    void visitInstruction(Instruction &I);

    bool visitIntrinsic(CallSite CS, Function* F);
    void visitCallSite(CallSite CS);
    void visitVAStart(CallSite CS);
    void visitVAStartNode(DSNode* N);

  public:
    GraphBuilder(Function &f, DSGraph &g, LocalDataStructures& DSi)
      : G(g), FB(&f), DS(&DSi), TD(g.getDataLayout()), VAArray(0) {
      // Create scalar nodes for all pointer arguments...
      for (Function::arg_iterator I = f.arg_begin(), E = f.arg_end();
           I != E; ++I) {
        if (isa<PointerType>(I->getType())) {
          // WD: Why do we set the external marker so early in the analysis?
          // Functions we have definitions for, but are externally reachable have no external contexts
          // that we'd want to BU external information into (since those contexts are by definition
          // ones we don't have code for).  Shouldn't this just be set in TD?
#if 0
          DSNode * Node = getValueDest(I).getNode();

          if (!f.hasInternalLinkage() || !f.hasPrivateLinkage())
            Node->setExternalMarker();
#else
          getValueDest(I).getNode();
#endif

        }
      }

      // Create an entry for the return, which tracks which functions are in
      // the graph
      g.getOrCreateReturnNodeFor(f);

      // Create a node to handle information about variable arguments
      g.getOrCreateVANodeFor(f);

      visit(f);  // Single pass over the function

      // If there are any constant globals referenced in this function, merge
      // their initializers into the local graph from the globals graph.
      // This resolves indirect calls in some common cases
      // Only merge info for nodes that already exist in the local pass
      // otherwise leaf functions could contain less collapsing than the globals
      // graph
      if (g.getScalarMap().global_begin() != g.getScalarMap().global_end()) {
        ReachabilityCloner RC(&g, g.getGlobalsGraph(), 0);
        for (DSScalarMap::global_iterator I = g.getScalarMap().global_begin(),
             E = g.getScalarMap().global_end(); I != E; ++I) {
          if (const GlobalVariable * GV = dyn_cast<GlobalVariable > (*I))
            if (GV->isConstant())
              RC.merge(g.getNodeForValue(GV), g.getGlobalsGraph()->getNodeForValue(GV));
        }
      }

      g.markIncompleteNodes(DSGraph::MarkFormalArgs);

      // Compute sources of external
      unsigned EFlags = 0
        | DSGraph::DontMarkFormalsExternal
        | DSGraph::ProcessCallSites;

      g.computeExternalFlags(EFlags);
      g.computeIntPtrFlags();

      // Remove any nodes made dead due to merging...
      g.removeDeadNodes(DSGraph::KeepUnreachableGlobals);
    }

    // GraphBuilder ctor for working on the globals graph
    explicit GraphBuilder(DSGraph& g)
      :G(g), FB(0), TD(g.getDataLayout()), VAArray(0)
    {}

    void mergeInGlobalInitializer(GlobalVariable *GV);
    void mergeExternalGlobal(GlobalVariable* GV);
    void mergeFunction(Function* F) { getValueDest(F); }
  };

  /// Traverse the whole DSGraph, and propagate the unknown flags through all 
  /// out edges.
  static void propagateUnknownFlag(DSGraph * G) {
    std::vector<DSNode *> workList;
    DenseSet<DSNode *> visited;
    for (DSGraph::node_iterator I = G->node_begin(), E = G->node_end(); I != E; ++I)
      if (I->isUnknownNode()) 
        workList.push_back(&*I);
  
    while (!workList.empty()) {
      DSNode * N = workList.back();
      workList.pop_back();
      if (visited.count(N) != 0) continue;
      visited.insert(N);
      N->setUnknownMarker();
      for (DSNode::edge_iterator I = N->edge_begin(), E = N->edge_end(); I != E; ++I)
        if (!I->second.isNull())
          workList.push_back(I->second.getNode());
    }
  }
}

//===----------------------------------------------------------------------===//
// Helper method implementations...
//


///
/// getValueDest - Return the DSNode that the actual value points to.
///
DSNodeHandle GraphBuilder::getValueDest(Value* V) {
  if (isa<Constant>(V) && cast<Constant>(V)->isNullValue()) 
    return 0;  // Null doesn't point to anything, don't add to ScalarMap!

  DSNodeHandle &NH = G.getNodeForValue(V);
  if (!NH.isNull())
    return NH;     // Already have a node?  Just return it...

  // Otherwise we need to create a new node to point to.
  // Check first for constant expressions that must be traversed to
  // extract the actual value.
  DSNode* N;
  if (Function * F = dyn_cast<Function > (V)) {
    // Create a new global node for this function.
    N = createNode();
    N->addFunction(F);
    if (F->isDeclaration())
      N->setExternFuncMarker();
  } else if (GlobalValue * GV = dyn_cast<GlobalValue > (V)) {
    // Create a new global node for this global variable.
    N = createNode();
    N->addGlobal(GV);
    if (GV->isDeclaration())
      N->setExternGlobalMarker();
  } else if (Constant *C = dyn_cast<Constant>(V)) {
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
      if (CE->isCast()) {
        if (isa<PointerType>(CE->getOperand(0)->getType()))
          NH = getValueDest(CE->getOperand(0));
        else
          NH = createNode()->setUnknownMarker();
      } else if (CE->getOpcode() == Instruction::GetElementPtr) {
        visitGetElementPtrInst(*CE);
        assert(G.hasNodeForValue(CE) && "GEP didn't get processed right?");
        NH = G.getNodeForValue(CE);
      } else {
        // This returns a conservative unknown node for any unhandled ConstExpr
        NH = createNode()->setUnknownMarker();
      }
      if (NH.isNull()) {  // (getelementptr null, X) returns null
        G.eraseNodeForValue(V);
        return 0;
      }
      return NH;
    } else if (isa<UndefValue>(C)) {
      G.eraseNodeForValue(V);
      return 0;
    } else if (isa<GlobalAlias>(C)) {
      // XXX: Need more investigation
      // According to Andrew, DSA is broken on global aliasing, since it does
      // not handle the aliases of parameters correctly. Here is only a quick
      // fix for some special cases.
      NH = getValueDest(cast<GlobalAlias>(C)->getAliasee());
      return NH;
    } else if (isa<BlockAddress>(C)) {
      //
      // FIXME: This may not be quite right; we should probably add a
      // BlockAddress flag to the DSNode instead of using the unknown flag.
      //
      N = createNode();
      N->setUnknownMarker();
    } else if (isa<ConstantStruct>(C) || isa<ConstantArray>(C) ||
               isa<ConstantDataSequential>(C) || isa<ConstantDataArray>(C) ||
               isa<ConstantDataVector>(C)) {
      // Treat these the same way we treat global initializers
      N = createNode();
      NH.mergeWith(N);
      MergeConstantInitIntoNode(NH, C->getType(), C);
    } else {
      errs() << "Unknown constant: " << *C << "\n";
      assert(0 && "Unknown constant type!");
    }
    N = createNode(); // just create a shadow node
  } else {
    // Otherwise just create a shadow node
    N = createNode();
  }

  NH.setTo(N, 0);      // Remember that we are pointing to it...
  return NH;
}


/// getLink - This method is used to return the specified link in the
/// specified node if one exists.  If a link does not already exist (it's
/// null), then we create a new node, link it, then return it.  We must
/// specify the type of the Node field we are accessing so that we know what
/// type should be linked to if we need to create a new node.
///
DSNodeHandle &GraphBuilder::getLink(const DSNodeHandle &node, unsigned LinkNo) {
  DSNodeHandle &Node = const_cast<DSNodeHandle&>(node);
  DSNodeHandle &Link = Node.getLink(LinkNo);
  if (Link.isNull()) {
    // If the link hasn't been created yet, make and return a new shadow node
    Link = createNode();
  }
  return Link;
}


/// setDestTo - Set the ScalarMap entry for the specified value to point to the
/// specified destination.  If the Value already points to a node, make sure to
/// merge the two destinations together.
///
void GraphBuilder::setDestTo(Value &V, const DSNodeHandle &NH) {
  G.getNodeForValue(&V).mergeWith(NH);
}


//===----------------------------------------------------------------------===//
// Specific instruction type handler implementations...
//

// PHINode - Make the scalar for the PHI node point to all of the things the
// incoming values point to... which effectively causes them to be merged.
//
void GraphBuilder::visitPHINode(PHINode &PN) {
  if (!isa<PointerType>(PN.getType())) return; // Only pointer PHIs

  DSNodeHandle &PNDest = G.getNodeForValue(&PN);
  for (unsigned i = 0, e = PN.getNumIncomingValues(); i != e; ++i)
    PNDest.mergeWith(getValueDest(PN.getIncomingValue(i)));
}

void GraphBuilder::visitSelectInst(SelectInst &SI) {
  if (!isa<PointerType>(SI.getType()))
    return; // Only pointer Selects

  DSNodeHandle &Dest = G.getNodeForValue(&SI);
  DSNodeHandle S1 = getValueDest(SI.getOperand(1));
  DSNodeHandle S2 = getValueDest(SI.getOperand(2));
  Dest.mergeWith(S1);
  Dest.mergeWith(S2);
}

void GraphBuilder::visitLoadInst(LoadInst &LI) {
  //
  // Create a DSNode for the pointer dereferenced by the load.  If the DSNode
  // is NULL, do nothing more (this can occur if the load is loading from a
  // NULL pointer constant (bugpoint can generate such code).
  //
  DSNodeHandle Ptr = getValueDest(LI.getPointerOperand());
  if (Ptr.isNull()) return; // Load from null

  // Make that the node is read from...
  Ptr.getNode()->setReadMarker();

  // Ensure a typerecord exists...
  Ptr.getNode()->growSizeForType(LI.getType(), Ptr.getOffset());

  if (isa<PointerType>(LI.getType()))
    setDestTo(LI, getLink(Ptr));

  // check that it is the inserted value
  if(TypeInferenceOptimize)
    if(LI.hasOneUse())
      if(StoreInst *SI = dyn_cast<StoreInst>(*(LI.use_begin())))
        if(SI->getOperand(0) == &LI) {
        ++NumIgnoredInst;
        return;
      }
  Ptr.getNode()->mergeTypeInfo(LI.getType(), Ptr.getOffset());
}

void GraphBuilder::visitStoreInst(StoreInst &SI) {
  Type *StoredTy = SI.getOperand(0)->getType();
  DSNodeHandle Dest = getValueDest(SI.getOperand(1));
  if (Dest.isNull()) return;

  // Mark that the node is written to...
  Dest.getNode()->setModifiedMarker();

  // Ensure a type-record exists...
  Dest.getNode()->growSizeForType(StoredTy, Dest.getOffset());

  // Avoid adding edges from null, or processing non-"pointer" stores
  if (isa<PointerType>(StoredTy))
    Dest.addEdgeTo(getValueDest(SI.getOperand(0)));

  if(TypeInferenceOptimize)
    if(SI.getOperand(0)->hasOneUse())
      if(isa<LoadInst>(SI.getOperand(0))){
        ++NumIgnoredInst;
        return;
      }
  Dest.getNode()->mergeTypeInfo(StoredTy, Dest.getOffset());
}

void GraphBuilder::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
  if (isa<PointerType>(I.getType())) {
    visitInstruction (I);
    return;
  }

  //
  // Create a DSNode for the dereferenced pointer .  If the DSNode is NULL, do
  // nothing more (this can occur if the pointer is a NULL constant; bugpoint
  // can generate such code).
  //
  DSNodeHandle Ptr = getValueDest(I.getPointerOperand());
  if (Ptr.isNull()) return;

  //
  // Make that the memory object is read and written.
  //
  Ptr.getNode()->setReadMarker();
  Ptr.getNode()->setModifiedMarker();

  //
  // If the result of the compare-and-swap is a pointer, then we need to do
  // a few things:
  //  o Merge the compare and swap values (which are pointers) with the result
  //  o Merge the DSNode of the pointer *within* the memory object with the
  //    DSNode of the compare, swap, and result DSNode.
  //
  if (isa<PointerType>(I.getType())) {
    //
    // Get the DSNodeHandle of the memory object returned from the load.  Make
    // it the DSNodeHandle of the instruction's result.
    //
    DSNodeHandle FieldPtr = getLink (Ptr);
    setDestTo(I, getLink(Ptr));

    //
    // Merge the result, compare, and swap values of the instruction.
    //
    FieldPtr.mergeWith (getValueDest (I.getCompareOperand()));
    FieldPtr.mergeWith (getValueDest (I.getNewValOperand()));
  }

  //
  // Modify the DSNode so that it has the loaded/written type at the
  // appropriate offset.
  //
  Ptr.getNode()->growSizeForType(I.getType(), Ptr.getOffset());
  Ptr.getNode()->mergeTypeInfo(I.getType(), Ptr.getOffset());
  return;
}

void GraphBuilder::visitAtomicRMWInst(AtomicRMWInst &I) {
  //
  // Create a DSNode for the dereferenced pointer .  If the DSNode is NULL, do
  // nothing more (this can occur if the pointer is a NULL constant; bugpoint
  // can generate such code).
  //
  DSNodeHandle Ptr = getValueDest(I.getPointerOperand());
  if (Ptr.isNull()) return;

  //
  // Make that the memory object is read and written.
  //
  Ptr.getNode()->setReadMarker();
  Ptr.getNode()->setModifiedMarker();

  //
  // Modify the DSNode so that it has the loaded/written type at the
  // appropriate offset.
  //
  Ptr.getNode()->growSizeForType(I.getType(), Ptr.getOffset());
  Ptr.getNode()->mergeTypeInfo(I.getType(), Ptr.getOffset());
  return;
}

void GraphBuilder::visitReturnInst(ReturnInst &RI) {
  if (RI.getNumOperands() && isa<PointerType>(RI.getOperand(0)->getType()))
    G.getOrCreateReturnNodeFor(*FB).mergeWith(getValueDest(RI.getOperand(0)));
}

void GraphBuilder::visitVAArgInst(VAArgInst &I) {
  Module *M = FB->getParent();
  Triple TargetTriple(M->getTargetTriple());
  Triple::ArchType Arch = TargetTriple.getArch();
  switch(Arch) {
  case Triple::x86_64: {
    // On x86_64, we have va_list as a struct {i32, i32, i8*, i8* }
    // The first i8* is where arguments generally go, but the second i8* can
    // be used also to pass arguments by register.
    // We model this by having both the i8*'s point to an array of pointers
    // to the arguments.
    DSNodeHandle Ptr = G.getVANodeFor(*FB);
    DSNodeHandle Dest = getValueDest(&I);
    if (Ptr.isNull()) return;

    // Make that the node is read and written
    Ptr.getNode()->setReadMarker()->setModifiedMarker();

    // Not updating type info, as it is already a collapsed node

    if (isa<PointerType>(I.getType()))
      Dest.mergeWith(Ptr);
    return; 
  }

  default: {
    assert(0 && "What frontend generates this?");
    DSNodeHandle Ptr = getValueDest(I.getOperand(0));

    //FIXME: also updates the argument
    if (Ptr.isNull()) return;

    // Make that the node is read and written
    Ptr.getNode()->setReadMarker()->setModifiedMarker();

    // Ensure a type record exists.
    DSNode *PtrN = Ptr.getNode();
    PtrN->mergeTypeInfo(I.getType(), Ptr.getOffset());

    if (isa<PointerType>(I.getType()))
      setDestTo(I, getLink(Ptr));
  }
  }
}

void GraphBuilder::visitIntToPtrInst(IntToPtrInst &I) {
  DSNode *N = createNode();
  if(I.hasOneUse()) {
    if(isa<ICmpInst>(*(I.use_begin()))) {
      NumBoringIntToPtr++;
      return;
    }
  } else {
    N->setIntToPtrMarker();
    N->setUnknownMarker();
  }
  setDestTo(I, N); 
}

void GraphBuilder::visitPtrToIntInst(PtrToIntInst& I) {
  DSNode* N = getValueDest(I.getOperand(0)).getNode();
  if(I.hasOneUse()) {
    if(isa<ICmpInst>(*(I.use_begin()))) {
      NumBoringIntToPtr++;
      return;
    }
  }
  if(I.hasOneUse()) {
    Value *V = dyn_cast<Value>(*(I.use_begin()));
    DenseSet<Value *> Seen;
    while(V && V->hasOneUse() &&
          Seen.insert(V).second) {
      if(isa<LoadInst>(V))
        break;
      if(isa<StoreInst>(V))
        break;
      if(isa<CallInst>(V))
        break;
      V = dyn_cast<Value>(*(V->use_begin()));
    }
    if(isa<BranchInst>(V)){
      NumBoringIntToPtr++;
      return;
    }
  }
  if(N)
    N->setPtrToIntMarker();
}


void GraphBuilder::visitBitCastInst(BitCastInst &I) {
  if (!isa<PointerType>(I.getType())) return; // Only pointers
  DSNodeHandle Ptr = getValueDest(I.getOperand(0));
  if (Ptr.isNull()) return;
  setDestTo(I, Ptr);
}

void GraphBuilder::visitCmpInst(CmpInst &I) {
  //Address can escape through cmps
}

unsigned getValueOffset(Type *Ty, ArrayRef<unsigned> Idxs,
                        const DataLayout &TD) {
  unsigned Offset = 0;
  for (ArrayRef<unsigned>::iterator I = Idxs.begin(), E = Idxs.end(); I != E;
       ++I) {
    // Lifted from DataLayout.cpp's getIndexedOffset.
    // We can't use that because it insists on only allowing pointer types.
    if (StructType *STy = dyn_cast<StructType>(Ty)) {
      unsigned FieldNo = *I;

      // Get structure layout information...
      const StructLayout *Layout = TD.getStructLayout(STy);

      // Add in the offset, as calculated by the structure layout info...
      Offset += Layout->getElementOffset(FieldNo);

      // Update Ty to refer to current element
      Ty = STy->getElementType(FieldNo);
    } else {
      // Update Ty to refer to current element
      Ty = cast<SequentialType>(Ty)->getElementType();

      // Get the array index and the size of each array element.
      int64_t arrayIdx = *I;
      Offset += (uint64_t)arrayIdx * TD.getTypeAllocSize(Ty);
    }
  }
  return Offset;
}

void GraphBuilder::visitInsertValueInst(InsertValueInst& I) {
  setDestTo(I, createNode()->setAllocaMarker());

  Type *StoredTy = I.getInsertedValueOperand()->getType();
  DSNodeHandle Dest = getValueDest(&I);
  Dest.mergeWith(getValueDest(I.getAggregateOperand()));

  // Mark that the node is written to...
  Dest.getNode()->setModifiedMarker();
  Type* STy = I.getAggregateOperand()->getType();

  unsigned Offset = getValueOffset(STy, I.getIndices(), TD);

  // Ensure a type-record exists...
  Dest.getNode()->mergeTypeInfo(StoredTy, Offset);

  // Avoid adding edges from null, or processing non-"pointer" stores
  if (isa<PointerType>(StoredTy))
    Dest.addEdgeTo(getValueDest(I.getInsertedValueOperand()));
}

void GraphBuilder::visitExtractValueInst(ExtractValueInst& I) {
  DSNodeHandle Ptr = getValueDest(I.getAggregateOperand());

  // Make that the node is read from...
  Ptr.getNode()->setReadMarker();
  Type* STy = I.getAggregateOperand()->getType();

  unsigned Offset = getValueOffset(STy, I.getIndices(), TD);

  // Ensure a typerecord exists...
  Ptr.getNode()->mergeTypeInfo(I.getType(), Offset);

  if (isa<PointerType>(I.getType()))
    setDestTo(I, getLink(Ptr));
}

void GraphBuilder::visitGetElementPtrInst(User &GEP) {
  //
  // Ensure that the indexed pointer has a DSNode.
  //
  DSNodeHandle NodeH = getValueDest(GEP.getOperand(0));
  if (NodeH.isNull())
    NodeH = createNode();

  //
  // There are a few quick and easy cases to handle.  If  the DSNode of the 
  // indexed pointer is already folded, then we know that the result of the 
  // GEP will have the same offset into the same DSNode 
  // as the indexed pointer.
  //

  if (!NodeH.isNull() &&
      NodeH.getNode()->isNodeCompletelyFolded()) {
    setDestTo(GEP, NodeH);
    return;
  }

  //
  // Okay, no easy way out.  Calculate the offset into the object being
  // indexed.
  //

  int Offset = 0;

  // FIXME: I am not sure if the code below is completely correct (especially
  //        if we start doing fancy analysis on non-constant array indices).
  //        What if the array is indexed using a larger index than its declared
  //        size?  Does the LLVM verifier catch such issues?
  //

  //
  // Determine the offset (in bytes) between the result of the GEP and the
  // GEP's pointer operand.
  //
  // Note: All of these subscripts are indexing INTO the elements we have...
  //
  // FIXME: We can do better for array indexing.  First, if the array index is
  //        constant, we can determine how much farther we're moving the
  //        pointer.  Second, we can try to use the results of other analysis
  //        passes (e.g., ScalarEvolution) to find min/max values to do less
  //        conservative type-folding.
  //
  for (gep_type_iterator I = gep_type_begin(GEP), E = gep_type_end(GEP);
       I != E; ++I)
    if (StructType *STy = dyn_cast<StructType>(*I)) {
      // indexing into a structure
      // next index must be a constant
      const ConstantInt* CUI = cast<ConstantInt>(I.getOperand());
      int FieldNo = CUI->getSExtValue();
      // increment the offset by the actual byte offset being accessed

      unsigned requiredSize = TD.getTypeAllocSize(STy) + NodeH.getOffset() + Offset;

      //
      // Grow the DSNode size as needed.
      //
      if (!NodeH.getNode()->isArrayNode() || NodeH.getNode()->getSize() <= 0){
        if (requiredSize > NodeH.getNode()->getSize())
          NodeH.getNode()->growSize(requiredSize);
      }

      Offset += (unsigned)TD.getStructLayout(STy)->getElementOffset(FieldNo);
      if (TypeInferenceOptimize) {
        if (ArrayType* AT = dyn_cast<ArrayType>(STy->getTypeAtIndex(FieldNo))) {
          NodeH.getNode()->mergeTypeInfo(AT, NodeH.getOffset() + Offset);
          if ((++I) == E) {
            break;
          }

          // Check if we are still indexing into an array.
          // We only record the topmost array type of any nested array.
          // Keep skipping indexes till we reach a non-array type.
          // J is the type of the next index.
          // Uncomment the line below to get all the nested types.
          gep_type_iterator J = I;
          while (isa<ArrayType>(*(++J))) {
            //      NodeH.getNode()->mergeTypeInfo(AT1, NodeH.getOffset() + Offset);
            if((++I) == E) {
              break;
            }
            J = I;
          }
          if ((I) == E) {
            break;
          }
        }
      }
    } else if (ArrayType *ATy = dyn_cast<ArrayType>(*I)) {
      // indexing into an array.
      NodeH.getNode()->setArrayMarker();
      Type *CurTy = ATy->getElementType();

      //
      // Ensure that the DSNode's size is large enough to contain one
      // element of the type to which the pointer points.
      //
      if (!isa<ArrayType>(CurTy) && NodeH.getNode()->getSize() <= 0) {
        NodeH.getNode()->growSize(TD.getTypeAllocSize(CurTy));
      } else if(isa<ArrayType>(CurTy) && NodeH.getNode()->getSize() <= 0){
        Type *ETy = (cast<ArrayType>(CurTy))->getElementType();
        while(isa<ArrayType>(ETy)) {
          ETy = (cast<ArrayType>(ETy))->getElementType();
        }
        NodeH.getNode()->growSize(TD.getTypeAllocSize(ETy));
      }

      // Find if the DSNode belongs to the array
      // If not fold.
      if((NodeH.getOffset() || Offset != 0)
         || (!isa<ArrayType>(CurTy)
             && (NodeH.getNode()->getSize() != TD.getTypeAllocSize(CurTy)))) {
        NodeH.getNode()->foldNodeCompletely();
        NodeH.getNode();
        Offset = 0;
        break;
      }
    } else if (const PointerType *PtrTy = dyn_cast<PointerType>(*I)) {
      // Get the type pointed to by the pointer
      Type *CurTy = PtrTy->getElementType();

      //
      // Some LLVM transforms lower structure indexing into byte-level
      // indexing.  Try to recognize forms of that here.
      //
      Type * Int8Type  = Type::getInt8Ty(CurTy->getContext());
      ConstantInt * IS = dyn_cast<ConstantInt>(I.getOperand());
      if (IS &&
          (NodeH.getOffset() == 0) &&
          (!(NodeH.getNode()->isArrayNode())) &&
          (CurTy == Int8Type)) {
        // Calculate the offset of the field
        Offset += IS->getSExtValue() * TD.getTypeAllocSize (Int8Type);

        //
        // Grow the DSNode size as needed.
        //
        unsigned requiredSize = Offset + TD.getTypeAllocSize (Int8Type);
        if (NodeH.getNode()->getSize() <= requiredSize){
          NodeH.getNode()->growSize (requiredSize);
        }

        // Add in the offset calculated...
        NodeH.setOffset(NodeH.getOffset()+Offset);

        // Check the offset
        DSNode *N = NodeH.getNode();
        if (N) N->checkOffsetFoldIfNeeded(NodeH.getOffset());

        // NodeH is now the pointer we want to GEP to be...
        setDestTo(GEP, NodeH);
        return;
      }

      //
      // Unless we're advancing the pointer by zero bytes via array indexing,
      // fold the node (i.e., mark it type-unknown) and indicate that we're
      // indexing zero bytes into the object (because all fields are aliased).
      //
      // Note that we break out of the loop if we fold the node.  Once
      // something is folded, all values within it are considered to alias.
      //
      if (!isa<Constant>(I.getOperand()) ||
          !cast<Constant>(I.getOperand())->isNullValue()) {

        //
        // Treat the memory object (DSNode) as an array.
        //
        NodeH.getNode()->setArrayMarker();

        //
        // Ensure that the DSNode's size is large enough to contain one
        // element of the type to which the pointer points.
        //
        if (!isa<ArrayType>(CurTy) && NodeH.getNode()->getSize() <= 0){
          NodeH.getNode()->growSize(TD.getTypeAllocSize(CurTy));
        } else if (isa<ArrayType>(CurTy) && NodeH.getNode()->getSize() <= 0){
          Type *ETy = (cast<ArrayType>(CurTy))->getElementType();
          while (isa<ArrayType>(ETy)) {
            ETy = (cast<ArrayType>(ETy))->getElementType();
          }
          NodeH.getNode()->growSize(TD.getTypeAllocSize(ETy));
        }

        //
        // Fold the DSNode if we're indexing into it in a type-incompatible
        // manner.  That can occur if:
        //  1) The DSNode represents a pointer into the object at a non-zero
        //     offset.
        //  2) The offset of the pointer is already non-zero.
        //  3) The size of the array element does not match the size into which
        //     the pointer indexing is indexing.
        //
        if (NodeH.getOffset() || Offset != 0 ||
            (!isa<ArrayType>(CurTy) &&
             (NodeH.getNode()->getSize() != TD.getTypeAllocSize(CurTy)))) {
          NodeH.getNode()->foldNodeCompletely();
          NodeH.getNode();
          Offset = 0;
          break;
        }
      }
    }

  // Add in the offset calculated...
  NodeH.setOffset(NodeH.getOffset()+Offset);

  // Check the offset
  DSNode *N = NodeH.getNode();
  if (N) N->checkOffsetFoldIfNeeded(NodeH.getOffset());

  // NodeH is now the pointer we want to GEP to be...
  setDestTo(GEP, NodeH);
}


void GraphBuilder::visitCallInst(CallInst &CI) {
  visitCallSite(&CI);
}

void GraphBuilder::visitInvokeInst(InvokeInst &II) {
  visitCallSite(&II);
}

void GraphBuilder::visitVAStart(CallSite CS) {
  // Build out DSNodes for the va_list depending on the target arch
  // And assosiate the right node with the VANode for this function
  // so it can be merged with the right arguments from callsites

  DSNodeHandle RetNH = getValueDest(CS.getArgument(0));

  if (DSNode *N = RetNH.getNode())
    visitVAStartNode(N);
}

void GraphBuilder::visitVAStartNode(DSNode* N) {
  assert(N && "Null node as argument");
  assert(FB && "No function for this graph?");
  Module *M = FB->getParent();
  assert(M && "No module for function");
  Triple TargetTriple(M->getTargetTriple());
  Triple::ArchType Arch = TargetTriple.getArch();

  // Fetch the VANode associated with the func containing the call to va_start
  DSNodeHandle & VANH = G.getVANodeFor(*FB);
  // Make sure this NodeHandle has a node to go with it
  if (VANH.isNull()) VANH.mergeWith(createNode());

  // Create a dsnode for an array of pointers to the VAInfo for this func
  // We create one such array for each function analyzed, as all
  // calls to va_start will populate their argument with the same data.
  if (!VAArray) VAArray = createNode();
  VAArray->setArrayMarker();
  VAArray->foldNodeCompletely();
  VAArray->setLink(0,VANH);

  //VAStart modifies its argument
  N->setModifiedMarker();

  // For the architectures we support, build dsnodes that match
  // how we know va_list is used.
  switch (Arch) {
  case Triple::x86:
    // On x86, we have:
    // va_list as a pointer to an array of pointers to the variable arguments
    if (N->getSize() < 1)
      N->growSize(1);
    N->setLink(0, VAArray);
    break;
  case Triple::x86_64:
    // On x86_64, we have va_list as a struct {i32, i32, i8*, i8* }
    // The first i8* is where arguments generally go, but the second i8* can
    // be used also to pass arguments by register.
    // We model this by having both the i8*'s point to an array of pointers
    // to the arguments.
    if (N->getSize() < 24)
      N->growSize(24); //sizeof the va_list struct mentioned above
    N->setLink(8,VAArray); //first i8*
    N->setLink(16,VAArray); //second i8*

    break;
  default:
    // FIXME: For now we abort if we don't know how to handle this arch
    // Either add support for other architectures, or at least mark the
    // nodes unknown/incomplete or whichever results in the correct
    // conservative behavior in the general case
    assert(0 && "VAstart not supported on this architecture!");
    //XXX: This might be good enough in those cases that we don't know
    //what the arch does
    N->setIncompleteMarker()->setUnknownMarker()->foldNodeCompletely();
  }

  // XXX: We used to set the alloca marker for the DSNode passed to va_start.
  // Seems to me that you could allocate the va_list on the heap, so ignoring
  // for now.
  N->setModifiedMarker()->setVAStartMarker();
}

///
/// Method: visitIntrinsic()
///
/// Description:
///   Generate correct DSNodes for calls to LLVM intrinsic functions.
///
/// Inputs:
///   CS - The CallSite representing the call or invoke to the intrinsic.
///   F  - A pointer to the function called by the call site.
///
/// Return value:
///   true  - This intrinsic is properly handled by this method.
///   false - This intrinsic is not recognized by DSA.
///
bool GraphBuilder::visitIntrinsic(CallSite CS, Function *F) {
  ++NumIntrinsicCall;

  //
  // If this is a debug intrinsic, then don't do any special processing.
  //
  if (isa<DbgInfoIntrinsic>(CS.getInstruction()))
    return true;

  switch (F->getIntrinsicID()) {
  case Intrinsic::vastart: {
    visitVAStart(CS);
    return true;
  }
  case Intrinsic::vacopy: {
    // Simply merge the two arguments to va_copy.
    // This results in loss of precision on the temporaries used to manipulate
    // the va_list, and so isn't a big deal.  In theory we would build a
    // separate graph for this (like the one created in visitVAStartNode)
    // and only merge the node containing the variable arguments themselves.
    DSNodeHandle destNH = getValueDest(CS.getArgument(0));
    DSNodeHandle srcNH = getValueDest(CS.getArgument(1));
    destNH.mergeWith(srcNH);
    return true;
  }
  case Intrinsic::stacksave: {
    DSNode * Node = createNode();
    Node->setAllocaMarker()->setIncompleteMarker()->setUnknownMarker();
    Node->foldNodeCompletely();
    setDestTo (*(CS.getInstruction()), Node);
    return true;
  }
  case Intrinsic::stackrestore:
    getValueDest(CS.getInstruction()).getNode()->setAllocaMarker()
      ->setIncompleteMarker()
      ->setUnknownMarker()
      ->foldNodeCompletely();
    return true;
  case Intrinsic::vaend:
    // TODO: What to do here?
    return true;
  case Intrinsic::memcpy: 
  case Intrinsic::memmove: {
    // Merge the first & second arguments, and mark the memory read and
    // modified.
    DSNodeHandle RetNH = getValueDest(CS.getArgument(0));
    RetNH.mergeWith(getValueDest(CS.getArgument(1)));
    if (DSNode *N = RetNH.getNode())
      N->setModifiedMarker()->setReadMarker();
    return true;
  }
  case Intrinsic::memset:
    // Mark the memory modified.
    if (DSNode *N = getValueDest(CS.getArgument(0)).getNode())
      N->setModifiedMarker();
    return true;

    // TODO: Add support for the new EH system
#if 0
  case Intrinsic::eh_exception: {
    DSNode * Node = createNode();
    Node->setIncompleteMarker();
    Node->foldNodeCompletely();
    setDestTo (*(CS.getInstruction()), Node);
    return true;
  }

  case Intrinsic::eh_selector: {
    for (CallSite::arg_iterator I = CS.arg_begin(), E = CS.arg_end();
         I != E; ++I) {
      if (isa<PointerType>((*I)->getType())) {
        DSNodeHandle Ptr = getValueDest(*I);
        if(Ptr.getNode()) {
          Ptr.getNode()->setReadMarker();
          Ptr.getNode()->setIncompleteMarker();
        }
      }
    }
    return true;
  }
#endif

  case Intrinsic::eh_typeid_for: {
    DSNodeHandle Ptr = getValueDest(CS.getArgument(0));
    Ptr.getNode()->setReadMarker();
    Ptr.getNode()->setIncompleteMarker();
    return true;
  }

  case Intrinsic::prefetch:
    return true;

  case Intrinsic::objectsize:
    return true;

    //
    // The return address/frame address aliases with the stack, 
    // is type-unknown, and should
    // have the unknown flag set since we don't know where it goes.
    //
  case Intrinsic::returnaddress:
  case Intrinsic::frameaddress: {
    DSNode * Node = createNode();
    Node->setAllocaMarker()->setIncompleteMarker()->setUnknownMarker();
    Node->foldNodeCompletely();
    setDestTo (*(CS.getInstruction()), Node);
    return true;
  }

  // Process lifetime intrinsics
  case Intrinsic::lifetime_start:
  case Intrinsic::lifetime_end:
  case Intrinsic::invariant_start:
  case Intrinsic::invariant_end:
    return true;

  default: {
    //ignore pointer free intrinsics
    if (!isa<PointerType>(F->getReturnType())) {
      bool hasPtr = false;
      for (Function::const_arg_iterator I = F->arg_begin(), E = F->arg_end();
           I != E && !hasPtr; ++I)
        if (isa<PointerType>(I->getType()))
          hasPtr = true;
      if (!hasPtr)
        return true;
    }

    DEBUG(errs() << "[dsa:local] Unhandled intrinsic: " << F->getName() << "\n");
    assert(0 && "Unhandled intrinsic");
    return false;
  }
  }
}

void GraphBuilder::visitCallSite(CallSite CS) {
  //
  // Get the called value.  Strip off any casts which are lossless.
  //
  Value *Callee = CS.getCalledValue()->stripPointerCasts();

  // Special case handling of certain libc allocation functions here.
  if (Function *F = dyn_cast<Function>(Callee))
    if (F->isIntrinsic() && visitIntrinsic(CS, F))
      return;

  //Can't do much about inline asm (yet!)
  if (isa<InlineAsm> (Callee)) {
    ++NumAsmCall;
    DSNodeHandle RetVal;
    Instruction *I = CS.getInstruction();
    if (isa<PointerType > (I->getType()))
      RetVal = getValueDest(I);

    // Calculate the arguments vector...
    for (CallSite::arg_iterator I = CS.arg_begin(), E = CS.arg_end(); I != E; ++I)
      if (isa<PointerType > ((*I)->getType()))
        RetVal.mergeWith(getValueDest(*I));
    if (!RetVal.isNull())
      RetVal.getNode()->foldNodeCompletely();
    return;
  }

  // Set up the return value...
  DSNodeHandle RetVal;
  Instruction *I = CS.getInstruction();
  if (isa<PointerType>(I->getType()))
    RetVal = getValueDest(I);

  DSNode *CalleeNode = 0;
  if (!isa<Function>(Callee)) {
    CalleeNode = getValueDest(Callee).getNode();
    if (CalleeNode == 0) {
      DEBUG(errs() << "WARNING: Program is calling through a null pointer?\n" << *I);
      return;  // Calling a null pointer?
    }
  }

  // NOTE: This code is identical to 'DSGraph::getDSCallSiteForCallSite',
  // the reason it's duplicated is because this calls getValueDest instead
  // of getNodeForValue to get the DSNodes for the arguments.  Since we're in
  // local it's possible that we need to create a DSNode for the argument, as
  // opposed to getNodeForValue which simply retrieves the existing node.


  //Get the FunctionType for the called function
  const FunctionType *CalleeFuncType = DSCallSite::FunctionTypeOfCallSite(CS);
  int NumFixedArgs = CalleeFuncType->getNumParams();

  // Sanity check--this really, really shouldn't happen
  if (!CalleeFuncType->isVarArg())
    assert(CS.arg_size() == static_cast<unsigned>(NumFixedArgs) &&
           "Too many arguments/incorrect function signature!");

  std::vector<DSNodeHandle> Args;
  Args.reserve(CS.arg_size());
  DSNodeHandle VarArgNH;

  // Calculate the arguments vector...
  // Add all fixed pointer arguments, then merge the rest together
  for (CallSite::arg_iterator I = CS.arg_begin(), E = CS.arg_end();
       I != E; ++I)
    if (isa<PointerType>((*I)->getType())) {
      DSNodeHandle ArgNode = getValueDest(*I);
      if (I - CS.arg_begin() < NumFixedArgs) {
        Args.push_back(ArgNode);
      } else {
        VarArgNH.mergeWith(ArgNode);
      }
    }

  // Add a new function call entry...
  if (CalleeNode) {
    ++NumIndirectCall;
    G.getFunctionCalls().push_back(DSCallSite(CS, RetVal, VarArgNH, CalleeNode,
                                              Args));
  } else {
    ++NumDirectCall;
    G.getFunctionCalls().push_back(DSCallSite(CS, RetVal, VarArgNH,
                                              cast<Function>(Callee),
                                              Args));
  }


}

// visitInstruction - For all other instruction types, if we have any arguments
// that are of pointer type, make them have unknown composition bits, and merge
// the nodes together.
void GraphBuilder::visitInstruction(Instruction &Inst) {
  DSNodeHandle CurNode;
  if (isa<PointerType>(Inst.getType()))
    CurNode = getValueDest(&Inst);
  for (User::op_iterator I = Inst.op_begin(), E = Inst.op_end(); I != E; ++I)
    if (isa<PointerType>((*I)->getType()))
      CurNode.mergeWith(getValueDest(*I));

  if (DSNode *N = CurNode.getNode())
    N->setUnknownMarker();
}



//===----------------------------------------------------------------------===//
// LocalDataStructures Implementation
//===----------------------------------------------------------------------===//

//
// Function: MergeConstantInitIntoNode()
//
// Description:
//  Merge the specified constant into the specified DSNode.
//
void
GraphBuilder::MergeConstantInitIntoNode(DSNodeHandle &NH,
                                        Type* Ty,
                                        Constant *C) {
  //
  // Ensure a type-record exists...
  //
  DSNode *NHN = NH.getNode();
  //NHN->mergeTypeInfo(Ty, NH.getOffset());

  //
  // If we've found something of pointer type, create or find its DSNode and
  // make a link from the specified DSNode to the new DSNode describing the
  // pointer we've just found.
  //
  if (isa<PointerType>(Ty)) {
    NHN->mergeTypeInfo(Ty, NH.getOffset());
    NH.addEdgeTo(getValueDest(C));
    return;
  }

  //
  // If the type of the object (array element, structure field, etc.) is an
  // integer or floating point type, then just ignore it.  It has no DSNode.
  //
  if (Ty->isIntOrIntVectorTy() || Ty->isFPOrFPVectorTy()) return;

  //
  // Handle aggregate constants.
  //
  if (ConstantArray *CA = dyn_cast<ConstantArray>(C)) {
    //
    // For an array, we don't worry about different elements pointing to
    // different objects; we essentially pretend that all array elements alias.
    //
    Type * ElementType = cast<ArrayType>(Ty)->getElementType();
    for (unsigned i = 0, e = CA->getNumOperands(); i != e; ++i) {
      Constant * ConstElement = cast<Constant>(CA->getOperand(i));
      MergeConstantInitIntoNode(NH, ElementType, ConstElement);
    }
  } else if (ConstantStruct *CS = dyn_cast<ConstantStruct>(C)) {
    //
    // For a structure, we need to merge each element of the constant structure
    // into the specified DSNode.  However, we must also handle structures that
    // end with a zero-length array ([0 x sbyte]); this is a common C idiom
    // that continues to plague the world.
    //
    //NHN->mergeTypeInfo(Ty, NH.getOffset());

    const StructLayout *SL = TD.getStructLayout(cast<StructType>(Ty));

    for (unsigned i = 0, e = CS->getNumOperands(); i != e; ++i) {
      DSNode *NHN = NH.getNode();
      if (SL->getElementOffset(i) < SL->getSizeInBytes()) {
        //
        // Get the type and constant value of this particular element of the
        // constant structure.
        //
        Type * ElementType = cast<StructType>(Ty)->getElementType(i);
        Constant * ConstElement = cast<Constant>(CS->getOperand(i));

        //
        // Get the offset (in bytes) into the memory object that we're
        // analyzing.
        //
        unsigned offset = NH.getOffset()+(unsigned)SL->getElementOffset(i);
        NHN->mergeTypeInfo(ElementType, offset);
        //
        // Create a new DSNodeHandle.  This DSNodeHandle will point to the same
        // DSNode as the one we're constructing for our caller; however, it
        // will point into a different offset into that DSNode.
        //
        DSNodeHandle NewNH (NHN, offset);
        assert ((NHN->isNodeCompletelyFolded() || (NewNH.getOffset() == offset))
                && "Need to resize DSNode!");

        //
        // Recursively merge in this element of the constant struture into the
        // DSNode.
        //
        MergeConstantInitIntoNode(NewNH, ElementType, ConstElement);
      } else if (SL->getElementOffset(i) == SL->getSizeInBytes()) {
        //
        // If this is one of those cute structures that ends with a zero-length
        // array, just fold the DSNode now and get it over with.
        //
        DEBUG(errs() << "Zero size element at end of struct\n" );
        NHN->foldNodeCompletely();
      } else {
        assert(0 && "type was smaller than offsets of struct layout indicate");
      }
    }
  } else if (isa<ConstantAggregateZero>(C) || isa<UndefValue>(C)) {
    //
    // Undefined values and NULL pointers have no DSNodes, so they do nothing.
    //
  } else if (isa<ConstantDataSequential>(C)) {
    //
    // ConstantDataSequential's are arrays of integers or floats, so they
    // have no DSNodes.  Nothing to do here.
    //
  } else {
    assert(0 && "Unknown constant type!");
  }
}

void GraphBuilder::mergeInGlobalInitializer(GlobalVariable *GV) {
  // Ensure that the global variable is not external
  assert(!GV->isDeclaration() && "Cannot merge in external global!");

  //
  // Get a node handle to the global node and merge the initializer into it.
  //
  DSNodeHandle NH = getValueDest(GV);

  //
  // Ensure that the DSNode is large enough to hold the new constant that we'll
  // be adding to it.
  //
  Type * ElementType = GV->getType()->getElementType();
  while(ArrayType *ATy = dyn_cast<ArrayType>(ElementType)) {
    ElementType = ATy->getElementType();
  }
  if(!NH.getNode()->isNodeCompletelyFolded()) {
    unsigned requiredSize = TD.getTypeAllocSize(ElementType) + NH.getOffset();
    if (NH.getNode()->getSize() < requiredSize){
      NH.getNode()->growSize (requiredSize);
    }
  }

  //
  // Do the actual merging in of the constant initializer.
  //
  MergeConstantInitIntoNode(NH, GV->getType()->getElementType(), GV->getInitializer());

}

void GraphBuilder::mergeExternalGlobal(GlobalVariable *GV) {
  // Get a node handle to the global node and merge the initializer into it.
  DSNodeHandle NH = getValueDest(GV);
}

// some evil programs use sections as linker generated arrays
// read a description of this behavior in and apply it
// format: numglobals section globals...
// terminates when numglobals == 0
void handleMagicSections(DSGraph* GlobalsGraph, Module& M) {
  std::ifstream msf(hasMagicSections.c_str(), std::ifstream::in);
  if (msf.good()) {
    //no checking happens here
    unsigned count = 0;
    msf >> count;
    while (count) {
      std::string section;
      msf >> section;
      svset<Value*> inSection;
      for (Module::iterator MI = M.begin(), ME = M.end();
           MI != ME; ++MI)
        if (MI->hasSection() && MI->getSection() == section)
          inSection.insert(MI);
      for (Module::global_iterator MI = M.global_begin(), ME = M.global_end();
           MI != ME; ++MI)
        if (MI->hasSection() && MI->getSection() == section)
          inSection.insert(MI);

      for (unsigned x = 0; x < count; ++x) {
        std::string global;
        msf >> global;
        Value* V = M.getNamedValue(global);
        if (V) {
          DSNodeHandle& DHV = GlobalsGraph->getNodeForValue(V);
          for (svset<Value*>::iterator SI = inSection.begin(),
               SE = inSection.end(); SI != SE; ++SI) {
            DEBUG(errs() << "Merging " << V->getName().str() << " with "
                  << (*SI)->getName().str() << "\n");
            GlobalsGraph->getNodeForValue(*SI).mergeWith(DHV);
          }
        }
      }
      msf >> count;
    }
  } else {
    errs() << "Failed to open magic sections file:" << hasMagicSections <<
      "\n";
  }
}

char LocalDataStructures::ID;

bool LocalDataStructures::runOnModule(Module &M) {
  init(&getAnalysis<DataLayout>());
  addrAnalysis = &getAnalysis<AddressTakenAnalysis>();

  // First step, build the globals graph.
  {
    GraphBuilder GGB(*GlobalsGraph);

    // Add initializers for all of the globals to the globals graph.
    for (Module::global_iterator I = M.global_begin(), E = M.global_end();
         I != E; ++I)
      if (!(I->hasSection() && I->getSection() == "llvm.metadata")) {
        if (I->isDeclaration())
          GGB.mergeExternalGlobal(I);
        else
          GGB.mergeInGlobalInitializer(I);
      }
    // Add Functions to the globals graph.
    for (Module::iterator FI = M.begin(), FE = M.end(); FI != FE; ++FI){
      if(addrAnalysis->hasAddressTaken(FI)) {
        GGB.mergeFunction(FI);
      }
    }
  }

  if (hasMagicSections.size())
    handleMagicSections(GlobalsGraph, M);

  // Next step, iterate through the nodes in the globals graph, unioning
  // together the globals into equivalence classes.
  formGlobalECs();

  // Iterate through the address taken functions in the globals graph,
  // collecting them in a list, to be used as target for call sites that
  // cant be resolved.
  formGlobalFunctionList();
  GlobalsGraph->maskIncompleteMarkers();

  // Calculate all of the graphs...
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
    if (!I->isDeclaration()) {
      DSGraph* G = new DSGraph(GlobalECs, getDataLayout(), *TypeSS, GlobalsGraph);
      GraphBuilder GGB(*I, *G, *this);
      G->getAuxFunctionCalls() = G->getFunctionCalls();
      setDSGraph(*I, G);
      propagateUnknownFlag(G);
      callgraph.insureEntry(I);
      G->buildCallGraph(callgraph, GlobalFunctionList, true);
      G->maskIncompleteMarkers();
      G->markIncompleteNodes(DSGraph::MarkFormalArgs
                             |DSGraph::IgnoreGlobals);
      cloneIntoGlobals(G, DSGraph::DontCloneCallNodes |
                       DSGraph::DontCloneAuxCallNodes |
                       DSGraph::StripAllocaBit);
      formGlobalECs();
      DEBUG(G->AssertGraphOK());
    }

  //GlobalsGraph->removeTriviallyDeadNodes();
  GlobalsGraph->markIncompleteNodes(DSGraph::MarkFormalArgs
                                    |DSGraph::IgnoreGlobals);
  GlobalsGraph->computeExternalFlags(DSGraph::ProcessCallSites);

  // Now that we've computed all of the graphs, and merged all of the info into
  // the globals graph, see if we have further constrained the globals in the
  // program if so, update GlobalECs and remove the extraneous globals from the
  // program.
  formGlobalECs();

  propagateUnknownFlag(GlobalsGraph);
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
    if (!I->isDeclaration()) {
      DSGraph *Graph = getOrCreateGraph(I);
      Graph->maskIncompleteMarkers();
      cloneGlobalsInto(Graph, DSGraph::DontCloneCallNodes |
                       DSGraph::DontCloneAuxCallNodes);
      Graph->markIncompleteNodes(DSGraph::MarkFormalArgs
                                 |DSGraph::IgnoreGlobals);
    }

  return false;
}

