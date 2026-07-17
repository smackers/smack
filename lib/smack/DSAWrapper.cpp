//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE for details.
//
#include "smack/DSAWrapper.h"
#include "seadsa/InitializePasses.hh"
#include "smack/Debug.h"
#include "smack/InitializePasses.h"
#include "smack/SmackOptions.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/FileSystem.h"

#include <set>
#include <unordered_map>
#include <vector>

#define DEBUG_TYPE "smack-dsa-wrapper"

namespace smack {

using namespace llvm;

void DSAWrapper::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequiredTransitive<seadsa::DsaAnalysis>();
}

bool DSAWrapper::runOnModule(llvm::Module &M) {
  dataLayout = &M.getDataLayout();
  SD = &getAnalysis<seadsa::DsaAnalysis>().getDsaAnalysis();
  // Use the entry-point function's graph as the fallback graph for
  // globals/constants. This must match SmackModuleGenerator's entryFunction
  // so that globalRefCount (built from DG) uses the same nodes as the
  // entry function's region representatives.
  Function *entryFn = nullptr;
  for (auto &F : M) {
    if (!F.isDeclaration() && SmackOptions::isEntryPoint(F.getName())) {
      entryFn = &F;
      break;
    }
  }
  if (!entryFn) {
    // Fallback: use the first defined function.
    for (auto &F : M) {
      if (!F.isDeclaration()) {
        entryFn = &F;
        break;
      }
    }
  }
  assert(entryFn && "Module must have at least one defined function.");
  DG = &SD->getGraph(*entryFn);
  // Print the graph in dot format when debugging
  SDEBUG(DG->writeGraph("main.mem.dot"));
  module = &M;
  collectStaticInits(M);
  collectMemOpds(M);
  countGlobalRefs();
  return false;
}

void DSAWrapper::collectStaticInits(llvm::Module &M) {
  staticInits.clear();
  std::set<seadsa::Graph *> seenGraphs;
  std::vector<seadsa::Graph *> graphs;

  for (auto &F : M) {
    if (F.isDeclaration() || !SD->hasGraph(F))
      continue;
    auto &graph = SD->getGraph(F);
    if (seenGraphs.insert(&graph).second)
      graphs.push_back(&graph);
  }

  for (GlobalVariable &GV : M.globals()) {
    if (!GV.hasInitializer())
      continue;

    for (auto *graph : graphs) {
      if (graph->hasCell(GV))
        staticInits.insert(graph->getCell(GV).getNode());
    }
  }
}

void DSAWrapper::collectMemOpds(llvm::Module &M) {
  memOpds.clear();
  for (auto &f : M) {
    for (inst_iterator I = inst_begin(&f), E = inst_end(&f); I != E; ++I) {
      if (MemCpyInst *memcpyInst = dyn_cast<MemCpyInst>(&*I)) {
        memOpds.insert(memcpyInst->getSource());
        memOpds.insert(memcpyInst->getDest());
      } else if (MemSetInst *memsetInst = dyn_cast<MemSetInst>(&*I))
        memOpds.insert(memsetInst->getDest());
    }
  }
}

void DSAWrapper::countGlobalRefs() {
  globalRefCount.clear();
  uniqueGlobalRefs.clear();
  std::set<seadsa::Graph *> seenGraphs;

  for (auto &F : *module) {
    if (F.isDeclaration() || !SD->hasGraph(F))
      continue;
    auto &graph = SD->getGraph(F);
    if (!seenGraphs.insert(&graph).second)
      continue;

    for (auto &g : graph.globals()) {
      auto &cellRef = g.second;
      auto *node = cellRef->getNode();
      assert(node && "Global values should have DSNodes.");
      if (!globalRefCount.count(node)) {
        globalRefCount[node] = 1;
        uniqueGlobalRefs[node] = dyn_cast<GlobalValue>(g.first);
      } else {
        globalRefCount[node]++;
        uniqueGlobalRefs[node] = nullptr;
      }
    }
  }
}

bool DSAWrapper::isStaticInitd(const seadsa::Node *n) {
  return staticInits.count(n) > 0;
}

bool DSAWrapper::isMemOpd(const llvm::Value *v) { return memOpds.count(v) > 0; }

bool DSAWrapper::isRead(const Value *V) {
  // Check if the value is read in any function's graph (conservative).
  // This is needed for CS-DSA where different functions have different graphs.
  for (auto &F : *module) {
    if (F.isDeclaration() || !SD->hasGraph(F))
      continue;
    auto &graph = SD->getGraph(F);
    if (graph.hasCell(*V)) {
      auto *node = graph.getCell(*V).getNode();
      if (node && node->isRead())
        return true;
    }
  }
  // Fallback: check the default graph.
  auto node = getNode(V);
  if (node)
    return node->isRead();
  return false;
}

unsigned DSAWrapper::getPointedTypeSize(const Value *v) {
  if (llvm::PointerType *t = llvm::dyn_cast<llvm::PointerType>(v->getType())) {
    llvm::Type *pointedType = t->getElementType();
    if (pointedType->isSized())
      return dataLayout->getTypeStoreSize(pointedType);
    else
      return UINT_MAX;
  } else
    llvm_unreachable("Type should be pointer.");
}

seadsa::Graph &DSAWrapper::getGraphForValue(const Value *v) {
  if (auto *I = dyn_cast<Instruction>(v))
    if (SD->hasGraph(*I->getParent()->getParent()))
      return SD->getGraph(*I->getParent()->getParent());
  if (auto *A = dyn_cast<Argument>(v))
    if (SD->hasGraph(*A->getParent()))
      return SD->getGraph(*A->getParent());
  // For globals/constants or when no per-function graph, use fallback.
  return *DG;
}

seadsa::Graph &DSAWrapper::getGraph(const Function &F) {
  return SD->getGraph(F);
}

bool DSAWrapper::hasGraph(const Function &F) const { return SD->hasGraph(F); }

bool DSAWrapper::isContextSensitive() const {
  return SD && SD->kind() == seadsa::GlobalAnalysisKind::CONTEXT_SENSITIVE;
}

unsigned DSAWrapper::getOffset(const Value *v) {
  auto &graph = getGraphForValue(v);
  if (!graph.hasCell(*v))
    return 0;
  return graph.getCell(*v).getOffset();
}

unsigned DSAWrapper::getOffset(const Value *v, const Function &F) {
  if (!SD->hasGraph(F))
    return getOffset(v);
  auto &graph = SD->getGraph(F);
  if (graph.hasCell(*v))
    return graph.getCell(*v).getOffset();
  // Translate through shared globals first (preserves field offsets).
  auto &src = getGraphForValue(v);
  if (&src != &graph && src.hasCell(*v)) {
    seadsa::Cell c;
    if (translateGlobalCell(v, src, graph, c)) {
      auto *n = c.getNode();
      unsigned long rawOff = c.getOffset();
      if (n->isOffsetCollapsed())
        return 0;
      if (n->isArray() && n->size() > 0)
        return (unsigned)(rawOff % n->size());
      return (unsigned)rawOff;
    }
    // Values not rooted at a global (e.g., allocas in init functions) are
    // not shared global memory; global-rooted values whose field-sensitive
    // translation fails fall back to the whole target node at offset zero,
    // matching Regions::idxTranslated's conservative fallback.
  }
  return 0;
}

const seadsa::Node *DSAWrapper::getNode(const Value *v) {
  auto &graph = getGraphForValue(v);
  if (!graph.hasCell(*v))
    return nullptr;
  auto node = graph.getCell(*v).getNode();
  assert(node && "Values should have nodes if they have cells.");
  return node;
}

bool DSAWrapper::translateGlobalCell(const Value *v, seadsa::Graph &src,
                                     seadsa::Graph &dst,
                                     seadsa::Cell &result) const {
  if (!src.hasCell(*v))
    return false;

  const auto *GV = dyn_cast<GlobalVariable>(getUnderlyingObject(v));
  if (!GV || !src.hasCell(*GV) || !dst.hasCell(*GV))
    return false;

  seadsa::Cell from = src.getCell(*GV);
  seadsa::Cell to = dst.getCell(*GV);
  seadsa::SimulationMapper mapper;
  if (!mapper.insert(from, to) || !mapper.isFunction())
    return false;

  result = mapper.get(src.getCell(*v));
  return !result.isNull();
}

const seadsa::Node *DSAWrapper::getNode(const Value *v, const Function &F) {
  if (!SD->hasGraph(F))
    return getNode(v);
  auto &graph = SD->getGraph(F);
  if (graph.hasCell(*v)) {
    auto node = graph.getCell(*v).getNode();
    assert(node && "Values should have nodes if they have cells.");
    return node;
  }
  // V might be from a different function (e.g., a GEP in __SMACK_static_init
  // when we're resolving in the entry function's context). Translate its
  // cell from its own graph through the globals the two graphs share; this
  // preserves field offsets, unlike stripping to the underlying object.
  auto &src = getGraphForValue(v);
  if (&src != &graph && src.hasCell(*v)) {
    seadsa::Cell c;
    if (translateGlobalCell(v, src, graph, c))
      return c.getNode();
    // Global-rooted values whose field-sensitive translation fails fall
    // back to the whole target node, matching Regions::idxTranslated's
    // conservative fallback; values not rooted at a global are not shared
    // global memory, so report no node and let the caller treat them as an
    // unknown region.
    const auto *GV = dyn_cast<GlobalVariable>(getUnderlyingObject(v));
    if (GV && graph.hasCell(*GV))
      return graph.getCell(*GV).getNode();
  }
  return nullptr;
}

bool DSAWrapper::isTypeSafe(const Value *v) {
  typedef std::unordered_map<unsigned, bool> FieldMap;
  typedef std::unordered_map<const seadsa::Node *, FieldMap> NodeMap;
  static NodeMap nodeMap;

  auto node = getNode(v);
  if (!node)
    return false;

  if (node->isOffsetCollapsed() || node->isExternal() || node->isIncomplete() ||
      node->isUnknown() || node->isIntToPtr() || node->isPtrToInt() ||
      isMemOpd(v))
    // We consider it type-unsafe to be safe for these cases
    return false;

  if (!nodeMap.count(node)) {
    // Iterate all the fields of a node to find out
    // the type-safety of each field. Then, we cache the results.
    FieldMap fieldMap;
    auto &types = node->types();
    std::set<unsigned> offsets;

    for (auto &t : types)
      offsets.insert(t.first);

    auto offsetIterator = offsets.begin();

    while (true) {
      if (offsetIterator == offsets.end())
        // We have reached the last field and exit the loop
        break;

      unsigned offset = *offsetIterator;

      auto &typeSet = types.find(offset)->second;

      auto ti = typeSet.begin();
      if (++ti != typeSet.end())
        // If there are multiple access types, then it's trivially type-unsafe.
        fieldMap[offset] = false;

      // Get the maximum length
      unsigned fieldLength = 0;
      for (auto &t : typeSet) {
        // TODO: fix the const_cast
        unsigned length =
            dataLayout->getTypeStoreSize(const_cast<llvm::Type *>(t));
        if (length > fieldLength)
          fieldLength = length;
      }

      // Check if the current field overlaps with the next *fields*
      for (auto oi = ++offsetIterator; oi != offsets.end(); ++oi) {
        unsigned next_offset = *oi;
        if (offset + fieldLength > next_offset) {
          // Overlaps; mark the current field and the next unsafe
          fieldMap[offset] = false;
          fieldMap[next_offset] = false;
        } else
          // If the current field doesn't overlap with the next one,
          // it certainly won't overlap with the rest.
          break;
      }

      if (!fieldMap.count(offset))
        fieldMap[offset] = true;
    }

    nodeMap[node] = fieldMap;
  }

  auto offset = getOffset(v);
  if (nodeMap[node].count(offset))
    return nodeMap[node][offset];
  else
    // Chances to hit this branch are when we visit memcpy/memset
    // pointer operands.
    return false;
}

bool DSAWrapper::isTypeSafe(const Value *v, const Function &F) {
  typedef std::unordered_map<unsigned, bool> FieldMap;
  typedef std::unordered_map<const seadsa::Node *, FieldMap> NodeMap;
  static NodeMap nodeMap;

  auto node = getNode(v, F);
  if (!node)
    return false;

  if (node->isOffsetCollapsed() || node->isExternal() || node->isIncomplete() ||
      node->isUnknown() || node->isIntToPtr() || node->isPtrToInt() ||
      isMemOpd(v))
    return false;

  if (!nodeMap.count(node)) {
    FieldMap fieldMap;
    auto &types = node->types();
    std::set<unsigned> offsets;
    for (auto &t : types)
      offsets.insert(t.first);
    auto offsetIterator = offsets.begin();
    while (true) {
      if (offsetIterator == offsets.end())
        break;
      unsigned offset = *offsetIterator;
      auto &typeSet = types.find(offset)->second;
      auto ti = typeSet.begin();
      if (++ti != typeSet.end())
        fieldMap[offset] = false;
      unsigned fieldLength = 0;
      for (auto &t : typeSet) {
        unsigned length =
            dataLayout->getTypeStoreSize(const_cast<llvm::Type *>(t));
        if (length > fieldLength)
          fieldLength = length;
      }
      for (auto oi = ++offsetIterator; oi != offsets.end(); ++oi) {
        unsigned next_offset = *oi;
        if (offset + fieldLength > next_offset) {
          fieldMap[offset] = false;
          fieldMap[next_offset] = false;
        } else
          break;
      }
      if (!fieldMap.count(offset))
        fieldMap[offset] = true;
    }
    nodeMap[node] = fieldMap;
  }

  auto offset = getOffset(v, F);
  if (nodeMap[node].count(offset))
    return nodeMap[node][offset];
  else
    return false;
}

unsigned DSAWrapper::getNumGlobals(const seadsa::Node *n) {
  if (globalRefCount.count(n))
    return globalRefCount[n];
  else
    return 0;
}

const GlobalValue *DSAWrapper::getUniqueGlobal(const seadsa::Node *n) const {
  auto it = uniqueGlobalRefs.find(n);
  return it == uniqueGlobalRefs.end() ? nullptr : it->second;
}

} // namespace smack

char smack::DSAWrapper::ID = 0;

using namespace smack;
using namespace seadsa;
INITIALIZE_PASS_BEGIN(DSAWrapper, "smack-dsa-wrapper",
                      "SMACK Data Structure Graph Based Alias Analysis Wrapper",
                      false, false)
INITIALIZE_PASS_DEPENDENCY(DsaAnalysis)
INITIALIZE_PASS_END(DSAWrapper, "smack-dsa-wrapper",
                    "SMACK Data Structure Graph Based Alias Analysis Wrapper",
                    false, false)
