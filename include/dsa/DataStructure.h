//===- DataStructure.h - Build data structure graphs ------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Implement the LLVM data structure analysis library.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_DATA_STRUCTURE_H
#define LLVM_ANALYSIS_DATA_STRUCTURE_H

#include "dsa/DSCallGraph.h"
#include "dsa/svset.h"
#include "dsa/super_set.h"
#include "dsa/AddressTakenAnalysis.h"
#include "dsa/AllocatorIdentification.h"

#include "llvm/Pass.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/CallSite.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/ADT/DenseSet.h"

#include <map>

namespace llvm {

class Type;
class Instruction;
class GlobalValue;
class DSGraph;
class DSCallSite;
class DSNode;
class DSNodeHandle;

FunctionPass *createDataStructureStatsPass();
FunctionPass *createDataStructureGraphCheckerPass();

class DataStructures : public ModulePass {
  typedef std::map<const Function*, DSGraph*> DSInfoTy;

  /// DataLayout, comes in handy
  const DataLayout* TD;

  /// Pass to get Graphs from
  DataStructures* GraphSource;

  /// Do we clone Graphs or steal them?
  bool Clone;

  /// do we reset the aux list to the func list?
  bool resetAuxCalls;

  /// Were are DSGraphs stolen by another pass?
  bool DSGraphsStolen;

  void buildGlobalECs(svset<const GlobalValue*>& ECGlobals);

  void eliminateUsesOfECGlobals(DSGraph& G, const svset<const GlobalValue*> &ECGlobals);

  // DSInfo, one graph for each function
  DSInfoTy DSInfo;

  // Name for printing
  const char* printname;

protected:

  /// The Globals Graph contains all information on the globals
  DSGraph *GlobalsGraph;

  /// GlobalECs - The equivalence classes for each global value that is merged
  /// with other global values in the DSGraphs.
  EquivalenceClasses<const GlobalValue*> GlobalECs;

  SuperSet<Type*>* TypeSS;

  // Callgraph, as computed so far
  DSCallGraph callgraph;
  // List of all address taken functions.
  // This is used as target, of indirect calls for any indirect call site with  // incomplete callee node.
  std::vector<const Function*> GlobalFunctionList; 

  void init(DataStructures* D, bool clone, bool useAuxCalls, bool copyGlobalAuxCalls, bool resetAux);
  void init(const DataLayout* T);

  void formGlobalECs();
  
  void cloneIntoGlobals(DSGraph* G, unsigned cloneFlags);
  void cloneGlobalsInto(DSGraph* G, unsigned cloneFlags);

  void restoreCorrectCallGraph();
  
  void formGlobalFunctionList();

  DataStructures(char & id, const char* name) 
    : ModulePass(id), TD(0), GraphSource(0), printname(name), GlobalsGraph(0) {  
    // For now, the graphs are owned by this pass
    DSGraphsStolen = false;
  }

public:
  /// print - Print out the analysis results...
  ///
  void print(llvm::raw_ostream &O, const Module *M) const;
  void dumpCallGraph() const;

  /// handleTest - Handles various user-specified testing options.
  /// Returns true iff the user specified for us to test something.
  ///
  bool handleTest(llvm::raw_ostream &O, const Module *M) const;

  virtual void releaseMemory();

  virtual bool hasDSGraph(const Function &F) const {
    return DSInfo.find(&F) != DSInfo.end();
  }

  /// getDSGraph - Return the data structure graph for the specified function.
  ///
  virtual DSGraph *getDSGraph(const Function &F) const {
    std::map<const Function*, DSGraph*>::const_iterator I = DSInfo.find(&F);
    assert(I != DSInfo.end() && "Function not in module!");
    return I->second;
  }

  void setDSGraph(const Function& F, DSGraph* G) {
    DSInfo[&F] = G;
  }

  DSGraph* getOrCreateGraph(const Function* F);

  DSGraph* getGlobalsGraph() const { return GlobalsGraph; }

  EquivalenceClasses<const GlobalValue*> &getGlobalECs() { return GlobalECs; }

  const DataLayout& getDataLayout() const { return *TD; }

  const DSCallGraph& getCallGraph() const { return callgraph; }

  SuperSet<Type*>& getTypeSS() const { return *TypeSS; }
  
  /// deleteValue/copyValue - Interfaces to update the DSGraphs in the program.
  /// These correspond to the interfaces defined in the AliasAnalysis class.
  void deleteValue(Value *V);
  void copyValue(Value *From, Value *To);
};

// BasicDataStructures - The analysis is a dummy one -- all pointers can points
// to all possible locations.
//
class BasicDataStructures : public DataStructures {
public:
  static char ID;
  BasicDataStructures() : DataStructures(ID, "basic.") {}
  ~BasicDataStructures() { releaseMemory(); }

  virtual bool runOnModule(Module &M);

  /// getAnalysisUsage - This obviously provides a data structure graph.
  ///
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<DataLayoutPass>();
    AU.setPreservesAll();
  }
};

// LocalDataStructures - The analysis that computes the local data structure
// graphs for all of the functions in the program.
//
// FIXME: This should be a Function pass that can be USED by a Pass, and would
// be automatically preserved.  Until we can do that, this is a Pass.
//
class LocalDataStructures : public DataStructures {
  AddressTakenAnalysis* addrAnalysis;
public:
  static char ID;
  LocalDataStructures() : DataStructures(ID, "local.") {}
  ~LocalDataStructures() { releaseMemory(); }

  virtual bool runOnModule(Module &M);

  /// getAnalysisUsage - This obviously provides a data structure graph.
  ///
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<DataLayoutPass>();
    AU.addRequired<AddressTakenAnalysis>();
    AU.setPreservesAll();
  }
};

// StdLibDataStructures - This analysis recognizes common standard c library
// functions and generates graphs for them.
class StdLibDataStructures : public DataStructures {
  void eraseCallsTo(Function* F);
  void processRuntimeCheck (Module & M, std::string name, unsigned arg);
  void processFunction(int x, Function *F);
  AllocIdentify *AllocWrappersAnalysis;
public:
  static char ID;
  StdLibDataStructures() : DataStructures(ID, "stdlib.") {}
  ~StdLibDataStructures() { releaseMemory(); }

  virtual bool runOnModule(Module &M);

  /// getAnalysisUsage - This obviously provides a data structure graph.
  ///
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<LocalDataStructures>();
    AU.addRequired<AllocIdentify>();
    AU.setPreservesAll();
  }
};

/// BUDataStructures - The analysis that computes the interprocedurally closed
/// data structure graphs for all of the functions in the program.  This pass
/// only performs a "Bottom Up" propagation (hence the name).
///
class BUDataStructures : public DataStructures {
protected:

  const char* debugname;


  // filterCallees -- Whether or not we filter out illegal callees
  // from the CallGraph.  This is useful while doing original BU,
  // but might be undesirable in other passes such as CBU/EQBU.
  bool filterCallees;
public:
  static char ID;
  //Child constructor (CBU)
  BUDataStructures(char & CID, const char* name, const char* printname,
      bool filter)
    : DataStructures(CID, printname), debugname(name), filterCallees(filter) {}
  //main constructor
  BUDataStructures()
    : DataStructures(ID, "bu."), debugname("dsa-bu"),
    filterCallees(true) {}
  ~BUDataStructures() { releaseMemory(); }

  virtual bool runOnModule(Module &M);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<StdLibDataStructures>();
    AU.setPreservesAll();
  }

protected:
  bool runOnModuleInternal(Module &M);

private:
  // Private typedefs
  typedef std::map<const Function*, unsigned> TarjanMap;
  typedef std::vector<const Function*>        TarjanStack;
  typedef svset<const Function*>              FuncSet;

  void postOrderInline (Module & M);
  unsigned calculateGraphs (const Function *F,
                            TarjanStack & Stack,
                            unsigned & NextID,
                            TarjanMap & ValMap);

  void calculateGraph(DSGraph* G);

  void CloneAuxIntoGlobal(DSGraph* G);

  void getAllCallees(const DSCallSite &CS, FuncSet &Callees);
  void getAllAuxCallees (DSGraph* G, FuncSet &Callees);
  void applyCallsiteFilter(const DSCallSite &DCS, FuncSet &Callees);
};

/// CompleteBUDataStructures - This is the exact same as the bottom-up graphs,
/// but we use take a completed call graph and inline all indirect callees into
/// their callers graphs, making the result more useful for things like pool
/// allocation.
///
class CompleteBUDataStructures : public  BUDataStructures {
protected:
  void buildIndirectFunctionSets (void);
public:
  static char ID;
  CompleteBUDataStructures(char & CID = ID, 
                           const char* name = "dsa-cbu", 
                           const char* printname = "cbu.")
    : BUDataStructures(CID, name, printname, false) {}
  ~CompleteBUDataStructures() { releaseMemory(); }

  virtual bool runOnModule(Module &M);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<BUDataStructures>();
    AU.setPreservesAll();
  }

};

/// EquivBUDataStructures - This is the same as the complete bottom-up graphs, but
/// with functions partitioned into equivalence classes and a single merged
/// DS graph for all functions in an equivalence class.  After this merging,
/// graphs are inlined bottom-up on the SCCs of the final (CBU) call graph.
///
class EquivBUDataStructures : public CompleteBUDataStructures {
  void mergeGraphsByGlobalECs();
  void verifyMerging();

public:
  static char ID;
  EquivBUDataStructures()
    : CompleteBUDataStructures(ID, "dsa-eq", "eq.") {}
  ~EquivBUDataStructures() { releaseMemory(); }

  virtual bool runOnModule(Module &M);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<CompleteBUDataStructures>();
    AU.setPreservesAll();
  }

};

/// TDDataStructures - Analysis that computes new data structure graphs
/// for each function using the closed graphs for the callers computed
/// by the bottom-up pass.
///
class TDDataStructures : public DataStructures {
  svset<const Function*> ExternallyCallable;

  /// CallerCallEdges - For a particular graph, we keep a list of these records
  /// which indicates which graphs call this function and from where.
  struct CallerCallEdge {
    DSGraph *CallerGraph;        // The graph of the caller function.
    const DSCallSite *CS;        // The actual call site.
    const Function *CalledFunction;    // The actual function being called.

    CallerCallEdge(DSGraph *G, const DSCallSite *cs, const Function *CF)
      : CallerGraph(G), CS(cs), CalledFunction(CF) {}

    bool operator<(const CallerCallEdge &RHS) const {
      return CallerGraph < RHS.CallerGraph ||
            (CallerGraph == RHS.CallerGraph && CS < RHS.CS);
    }
  };

  std::map<DSGraph*, std::vector<CallerCallEdge> > CallerEdges;


  // IndCallMap - We memoize the results of indirect call inlining operations
  // that have multiple targets here to avoid N*M inlining.  The key to the map
  // is a sorted set of callee functions, the value is the DSGraph that holds
  // all of the caller graphs merged together, and the DSCallSite to merge with
  // the arguments for each function.
  std::map<std::vector<const Function*>, DSGraph*> IndCallMap;

  bool useEQBU;

public:
  static char ID;
  TDDataStructures(char & CID = ID, const char* printname = "td.", bool useEQ = false)
    : DataStructures(CID, printname), useEQBU(useEQ) {}
  ~TDDataStructures();

  virtual bool runOnModule(Module &M);

  /// getAnalysisUsage - This obviously provides a data structure graph.
  ///
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    if (useEQBU) {
      AU.addRequired<EquivBUDataStructures>();
    } else {
      AU.addRequired<BUDataStructures>();
      AU.addPreserved<BUDataStructures>();
    }
    AU.setPreservesAll();
  }

private:
  void markReachableFunctionsExternallyAccessible(DSNode *N,
                                                  DenseSet<DSNode*> &Visited);

  void InlineCallersIntoGraph(DSGraph* G);
  void ComputePostOrder(const Function &F, DenseSet<DSGraph*> &Visited,
                        std::vector<DSGraph*> &PostOrder);
};

/// EQTDDataStructures - Analysis that computes new data structure graphs
/// for each function using the closed graphs for the callers computed
/// by the EQ bottom-up pass.
///
class EQTDDataStructures : public TDDataStructures {
public:
  static char ID;
  EQTDDataStructures()
    :TDDataStructures(ID, "eqtd.", true)
  {}
  ~EQTDDataStructures();
};

} // End llvm namespace

#endif
