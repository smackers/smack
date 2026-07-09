//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/Regions.h"
#include "seadsa/CallSite.hh"
#include "seadsa/Mapper.hh"
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/ErrorHandling.h"

#include <memory>
#include <tuple>

#define DEBUG_TYPE "regions"

namespace smack {

const DataLayout *Region::DL = nullptr;
DSAWrapper *Region::DSA = nullptr;

void Region::init(Module &M, Pass &P) {
  DL = &M.getDataLayout();
  DSA = &P.getAnalysis<DSAWrapper>();
}

bool Region::isSingleton(const Value *v, unsigned length, const Function *F) {
  // TODO can we do something for non-global nodes?
  auto node = F ? DSA->getNode(v, *F) : DSA->getNode(v);

  return node && !isAllocated(node) && DSA->getNumGlobals(node) == 1 &&
         !node->isArray() &&
         (F ? DSA->isTypeSafe(v, *F) : DSA->isTypeSafe(v)) &&
         !DSA->isMemOpd(v) &&
         // Statically initialized globals cannot be singletons because
         // CodifyStaticInits generates pointer-based stores ($store) for them
         // in __SMACK_static_init, which requires map-typed $M variables.
         !DSA->isStaticInitd(node);
}

bool Region::isAllocated(const seadsa::Node *N) {
  return N->isHeap() || N->isAlloca();
}

bool Region::isComplicated(const seadsa::Node *N) {
  return N->isIntToPtr() || N->isPtrToInt() || N->isExternal() ||
         N->isUnknown();
}

void Region::init(const Value *V, unsigned length, const Function *F) {
  Type *T = V->getType();
  assert(T->isPointerTy() && "Expected pointer argument.");
  T = T->getPointerElementType();
  context = &V->getContext();
  representative = (DSA && !dyn_cast<ConstantPointerNull>(V))
                       ? (F ? DSA->getNode(V, *F) : DSA->getNode(V))
                       : nullptr;
  this->type = T;
  this->offset = DSA ? (F ? DSA->getOffset(V, *F) : DSA->getOffset(V)) : 0;
  // A zero-length region (opaque/extern types have storage size 0, and
  // memset/memcpy may have constant length 0) is an empty interval that
  // overlaps nothing — not even an identical probe — so every idx() lookup
  // would create a fresh duplicate, and any fixpoint probing such a region
  // diverges while the region vector grows unboundedly. Clamp to one byte.
  this->length = std::max(length, 1u);

  singleton = DL && representative && isSingleton(V, length, F);
  allocated = !representative || isAllocated(representative);
  bytewise = DSA && SmackOptions::BitPrecise &&
             (SmackOptions::NoByteAccessInference ||
              (!representative ||
               !(F ? DSA->isTypeSafe(V, *F) : DSA->isTypeSafe(V))) ||
              T->isIntegerTy(8));
  incomplete = !representative || representative->isIncomplete();
  complicated = !representative || isComplicated(representative);
  collapsed = !representative || representative->isOffsetCollapsed();

  // A region is global-scope if it backs global variables, which are
  // accessed by multiple global-memory functions (entry points,
  // __SMACK_static_init, __SMACK_init_func*). All other regions
  // (stack allocas, heap) are local to their function.
  globalScope = !representative || DSA->getNumGlobals(representative) > 0;
}

Region::Region(const Value *V, const Function *F) {
  unsigned length =
      DSA ? DSA->getPointedTypeSize(V) : std::numeric_limits<unsigned>::max();
  init(V, length, F);
}

Region::Region(const Value *V, const Function *F, unsigned length) {
  init(V, length, F);
}

// A node that is never dereferenced has size 0, but a zero-length region is
// an empty interval that overlaps nothing — not even an identical probe — so
// idx() would create a fresh duplicate on every lookup (which also keeps the
// Phase 3 fixpoint from converging). Clamp to at least one byte.
Region::Region(const seadsa::Node *node, LLVMContext &ctx)
    : Region(node, 0,
             node ? std::max(node->size(), 1u)
                  : std::numeric_limits<unsigned>::max(),
             ctx) {}

Region::Region(const seadsa::Node *node, unsigned offset, unsigned length,
               LLVMContext &ctx) {
  context = &ctx;
  representative = node;
  type = nullptr;
  this->offset = offset;
  this->length = length;
  singleton = false;
  allocated = !representative || isAllocated(representative);
  bytewise = true;
  incomplete = !representative || representative->isIncomplete();
  complicated = !representative || isComplicated(representative);
  collapsed = !representative || representative->isOffsetCollapsed();
  globalScope = !representative || DSA->getNumGlobals(representative) > 0;
}

Region::Region(const seadsa::Node *node, unsigned offset, unsigned length,
               const Type *type, bool bytewise, LLVMContext &ctx) {
  context = &ctx;
  representative = node;
  this->type = type;
  this->offset = offset;
  this->length = length;
  singleton = false;
  allocated = !representative || isAllocated(representative);
  this->bytewise = bytewise;
  incomplete = !representative || representative->isIncomplete();
  complicated = !representative || isComplicated(representative);
  collapsed = !representative || representative->isOffsetCollapsed();
  globalScope = !representative || DSA->getNumGlobals(representative) > 0;
}

bool Region::isDisjoint(unsigned offset, unsigned length) {
  // Compute in 64 bits: offset + length wraps in 32 bits for the
  // unbounded-length regions (unknown memset/memcpy lengths, whole-node
  // regions), which would make an engulfing region appear disjoint.
  return (unsigned long)this->offset + this->length <= offset ||
         (unsigned long)offset + length <= this->offset;
}

bool Region::merge(Region &R) {
  auto before =
      std::make_tuple(offset, length, singleton, allocated, bytewise,
                      incomplete, complicated, collapsed, globalScope, type);
  bool collapse = type != R.type;
  unsigned long low = std::min(offset, R.offset);
  unsigned long high = std::max((unsigned long)offset + length,
                                (unsigned long)R.offset + R.length);
  offset = low;
  // Saturate so that offset + length never exceeds the unsigned range:
  // 32-bit wrap-around here makes extents non-monotonic under merging,
  // which lets the Phase 3 fixpoint oscillate (merge, then re-create).
  length = (unsigned)std::min(
      high - low, (unsigned long)std::numeric_limits<unsigned>::max() - low);
  singleton = singleton && R.singleton;
  allocated = allocated || R.allocated;
  bytewise = SmackOptions::BitPrecise && (bytewise || R.bytewise || collapse);
  incomplete = incomplete || R.incomplete;
  complicated = complicated || R.complicated;
  collapsed = collapsed || R.collapsed;
  globalScope = globalScope || R.globalScope;
  type = (bytewise || collapse) ? NULL : type;
  return before != std::make_tuple(offset, length, singleton, allocated,
                                   bytewise, incomplete, complicated, collapsed,
                                   globalScope, type);
}

void Region::mergeAttributes(const Region &R) {
  bool collapse = type != R.type;
  singleton = singleton && R.singleton;
  allocated = allocated || R.allocated;
  bytewise = SmackOptions::BitPrecise && (bytewise || R.bytewise || collapse);
  incomplete = incomplete || R.incomplete;
  complicated = complicated || R.complicated;
  collapsed = collapsed || R.collapsed;
  globalScope = globalScope || R.globalScope;
  type = (bytewise || collapse) ? NULL : type;
}

bool Region::overlaps(Region &R) {
  return (incomplete && R.incomplete) || (complicated && R.complicated) ||
         (representative == R.representative &&
          (collapsed || !isDisjoint(R.offset, R.length)));
}

void Region::print(raw_ostream &O) {
  // TODO identify the representative
  O << "<Node:";
  if (type)
    O << *type;
  else
    O << "*";
  O << ">[" << offset << "," << (offset + length) << "]{";
  if (singleton)
    O << "S";
  if (bytewise)
    O << "B";
  if (complicated)
    O << "C";
  if (incomplete)
    O << "I";
  if (collapsed)
    O << "L";
  if (allocated)
    O << "A";
  O << "}";
}

char Regions::ID;
RegisterPass<Regions> RegionsPass("smack-regions", "SMACK Memory Regions Pass");

void Regions::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  if (!SmackOptions::NoMemoryRegionSplitting)
    AU.addRequired<DSAWrapper>();
}

bool Regions::runOnModule(Module &M) {
  if (!SmackOptions::NoMemoryRegionSplitting) {
    Region::init(M, *this);
    DSA = &getAnalysis<DSAWrapper>();

    // The unified memory model binds all shared memory to the first entry
    // point's region numbering; a second entry point would emit its own
    // numbering against those maps and silently verify the wrong program.
    {
      unsigned entryCount = 0;
      for (auto &F : M)
        if (!F.isDeclaration() && F.hasName() &&
            SmackOptions::isEntryPoint(F.getName()))
          entryCount++;
      if (entryCount > 1)
        report_fatal_error(
            "context-sensitive memory regions currently support a single "
            "entry point; use one --entry-points function at a time");
    }

    // Phase 1: Build per-function regions from each function's instructions.
    // Each function gets its own region vector computed from its own CS graph.
    // Also visit formal params and call-site actual args so that call-site
    // mapping (Phase 3) doesn't create new regions or alter indices.
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      // Visit formal pointer parameters.
      for (auto &A : F.args())
        if (A.getType()->isPointerTy())
          idx(&A, &F);
      // Visit all instructions.
      currentFunction = &F;
      visit(const_cast<Function &>(F));
    }
    currentFunction = nullptr;
    // Visit actual pointer arguments at call sites (in the caller's context).
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          if (auto *CB = dyn_cast<CallBase>(&I)) {
            for (unsigned i = 0; i < CB->arg_size(); i++) {
              Value *arg = CB->getArgOperand(i);
              if (arg->getType()->isPointerTy())
                idx(arg, &F);
            }
          }
        }
      }
    }
    // Visit globals in each function's context that accesses them.
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (!DSA->hasGraph(F))
        continue;
      auto &graph = DSA->getGraph(F);
      for (auto &GV : M.globals()) {
        if (GV.getType()->isPointerTy() && graph.hasCell(GV))
          idx(&GV, &F);
      }
    }

    // Create regions for all DSA nodes reachable through pointer links
    // from existing regions. This ensures callers have regions for data
    // accessible through pointer indirection (e.g., **arg), which their
    // callees may access. Without this, call-site mappings would be
    // incomplete and regions that should be distinct would be merged.
    for (auto &F : M) {
      if (F.isDeclaration() || !DSA->hasGraph(F))
        continue;
      bool grew = true;
      while (grew) {
        grew = false;
        auto &regions = funcRegionVecs[&F];
        std::set<const seadsa::Node *> existing;
        for (auto &r : regions)
          if (r.getRepresentative())
            existing.insert(r.getRepresentative());
        unsigned origSize = regions.size();
        // idx() below can cascade-merge and shrink the vector; re-check the
        // live size so regions[i] never reads out of bounds.
        for (unsigned i = 0; i < origSize && i < regions.size(); i++) {
          auto *rep = regions[i].getRepresentative();
          if (!rep)
            continue;
          for (auto &link : rep->links()) {
            auto *target = link.second->getNode();
            if (target && !existing.count(target)) {
              existing.insert(target);
              Region R(target, F.getContext());
              unsigned before = regions.size();
              idx(R, &F);
              grew = grew || regions.size() > before;
            }
          }
        }
      }
    }
    // Phase 2: Compute per-function read/write sets (direct accesses).
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      FunctionRegionInfo &info = funcRegions[&F];
      for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
        if (auto *LI = dyn_cast<LoadInst>(&*I)) {
          info.readRegions.insert(idx(LI->getPointerOperand(), &F));
        } else if (auto *SI = dyn_cast<StoreInst>(&*I)) {
          info.modifiedRegions.insert(idx(SI->getPointerOperand(), &F));
        } else if (auto *AI = dyn_cast<AtomicCmpXchgInst>(&*I)) {
          unsigned r = idx(AI->getPointerOperand(), &F);
          info.readRegions.insert(r);
          info.modifiedRegions.insert(r);
        } else if (auto *AI = dyn_cast<AtomicRMWInst>(&*I)) {
          unsigned r = idx(AI->getPointerOperand(), &F);
          info.readRegions.insert(r);
          info.modifiedRegions.insert(r);
        } else if (auto *MSI = dyn_cast<MemSetInst>(&*I)) {
          unsigned length;
          if (auto CI = dyn_cast<ConstantInt>(MSI->getLength()))
            length = CI->getZExtValue();
          else
            length = std::numeric_limits<unsigned>::max();
          info.modifiedRegions.insert(idx(MSI->getDest(), &F, length));
        } else if (auto *MTI = dyn_cast<MemTransferInst>(&*I)) {
          unsigned length;
          if (auto CI = dyn_cast<ConstantInt>(MTI->getLength()))
            length = CI->getZExtValue();
          else
            length = std::numeric_limits<unsigned>::max();
          info.readRegions.insert(idx(MTI->getSource(), &F, length));
          info.modifiedRegions.insert(idx(MTI->getDest(), &F, length));
        }
      }
    }

    // Phase 3: Compute call-site mappings (callee region -> caller region).
    // Iterate because link-following may create new regions in callers,
    // which then need mappings computed for their own callers. Convergence
    // requires a pass with no structural change at all (no creations and no
    // merges) so that every mapping reflects the final region numbering;
    // comparing region counts is not enough since one merge plus one
    // creation in the same pass cancel out.
    const unsigned maxIters = 100;
    unsigned iter;
    for (iter = 0; iter < maxIters; iter++) {
      unsigned version = structuralVersion;
      computeCallSiteMappings(M);
      if (structuralVersion == version)
        break;
    }
    if (iter == maxIters)
      errs() << "SMACK warning: call-site region mappings did not stabilize "
                "after "
             << maxIters
             << " passes; some memory-region mappings may be incomplete\n";
    mappingsFinal = true;

    // Phase 3.5: Propagate region merges top-down through the call graph.
    // When a caller collapses two callee regions (maps both to the same
    // caller region), the callee must merge them to preserve the invariant
    // that regions never alias.
    propagateRegionMerges(M);
    if (droppedMappings)
      errs() << "SMACK warning: " << droppedMappings
             << " call-site region mapping(s) dropped during region merge "
                "propagation; callers may see stale memory for the affected "
                "regions (-debug-only=regions for details)\n";

    // Phase 3.6: Map global-backed regions of every function to the entry
    // function's regions. These are emitted as module-level memory maps
    // (which Corral's variable-tracking abstraction can reason about
    // lazily) instead of being threaded through procedure signatures.
    computeGlobalMemoryMappings(M);

    // Phase 3.7: Unify all remaining cross-function memory into
    // module-level maps by taking the transitive closure of the call-site
    // mappings. Threading memory maps through procedure signatures places
    // them beyond Corral's variable-tracking abstraction and inflates
    // every inlined instance with map parameters and copies; emitting
    // shared memory as globals keeps the encoding within the abstraction.
    // Only function-private regions remain procedure-local.
    unifySharedRegions(M);

    // Phase 4: Transitive closure of region access sets.
    computeFunctionRegions(M);

    // Phase 5: Procedure memory interfaces. Private regions stay local; only
    // regions reachable from formals/globals/returns are threaded through
    // calls.
    computeInterfaceRegions(M);
  }

  return false;
}

unsigned Regions::size(const Function *F) const {
  auto it = funcRegionVecs.find(F);
  if (it != funcRegionVecs.end())
    return it->second.size();
  return 0;
}

Region &Regions::get(const Function *F, unsigned R) {
  return funcRegionVecs[F][R];
}

unsigned Regions::idx(const Value *V, const Function *F) {
  SDEBUG(errs() << "[regions] for: " << *V << " in function: " << F->getName()
                << "\n");
  Region R(V, F);
  return idx(R, F);
}

unsigned Regions::idx(const Value *V, const Function *F, unsigned length) {
  SDEBUG(errs() << "[regions] for: " << *V << " with length " << length
                << " in function: " << F->getName() << "\n");
  Region R(V, F, length);
  return idx(R, F);
}

unsigned Regions::idx(Region &R, const Function *F) {
  auto &regions = funcRegionVecs[F];
  unsigned r;

  SDEBUG(errs() << "[regions]   using region: ");
  SDEBUG(R.print(errs()));
  SDEBUG(errs() << "\n");

  for (auto &alias : mergedRegionAliases[F]) {
    if (alias.first.overlaps(R)) {
      SDEBUG(errs() << "[regions]   found merged alias at index "
                    << alias.second << ": ");
      SDEBUG(alias.first.print(errs()));
      SDEBUG(errs() << "\n");
      return alias.second;
    }
  }

  for (r = 0; r < regions.size(); ++r) {
    if (regions[r].overlaps(R)) {

      SDEBUG(errs() << "[regions]   found overlap at index " << r << ": ");
      SDEBUG(regions[r].print(errs()));
      SDEBUG(errs() << "\n");

      // NOTE: a widening-only merge (extent or attribute change without an
      // erase) does not bump structuralVersion. Counting it would be more
      // precise — call-site mappings probed with pre-widening attributes go
      // stale — but in practice widening never quiesces on large inputs
      // (Phase 3 then always runs to its pass cap, and the state at cutoff
      // depends on pointer-keyed iteration order, making the output
      // nondeterministic). Regions absorb attributes monotonically, so the
      // index structure this version guards remains sound.
      regions[r].merge(R);

      SDEBUG(errs() << "[regions]   merged region: ");
      SDEBUG(regions[r].print(errs()));
      SDEBUG(errs() << "\n");

      break;
    }
  }

  if (r == regions.size()) {
    regions.emplace_back(R);
    structuralVersion++;

  } else {
    // In case R was merged with an existing region, we must now also merge
    // any other region which intersects with R. Erasing regions[q] shifts
    // every index above q, so all index-based bookkeeping (access sets,
    // call-site mappings, aliases) must be repaired alongside.
    unsigned q = r + 1;
    while (q < regions.size()) {
      if (regions[r].overlaps(regions[q])) {

        SDEBUG(errs() << "[regions]   found extra overlap at index " << q
                      << ": ");
        SDEBUG(regions[q].print(errs()));
        SDEBUG(errs() << "\n");

        regions[r].merge(regions[q]);
        regions.erase(regions.begin() + q);
        remapAfterMerge(F, r, q);

        SDEBUG(errs() << "[regions]   merged region: ");
        SDEBUG(regions[r].print(errs()));
        SDEBUG(errs() << "\n");

      } else {
        q++;
      }
    }
  }

  SDEBUG(errs() << "[regions]   returning index: " << r << "\n\n");

  return r;
}

void Regions::visitLoadInst(LoadInst &I) {
  assert(currentFunction && "currentFunction must be set during visit");
  idx(I.getPointerOperand(), currentFunction);
}

void Regions::visitStoreInst(StoreInst &I) {
  assert(currentFunction && "currentFunction must be set during visit");
  idx(I.getPointerOperand(), currentFunction);
}

void Regions::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
  assert(currentFunction && "currentFunction must be set during visit");
  idx(I.getPointerOperand(), currentFunction);
}

void Regions::visitAtomicRMWInst(AtomicRMWInst &I) {
  assert(currentFunction && "currentFunction must be set during visit");
  idx(I.getPointerOperand(), currentFunction);
}

void Regions::visitMemSetInst(MemSetInst &I) {
  assert(currentFunction && "currentFunction must be set during visit");
  unsigned length;

  if (auto CI = dyn_cast<ConstantInt>(I.getLength()))
    length = CI->getZExtValue();
  else
    length = std::numeric_limits<unsigned>::max();

  idx(I.getDest(), currentFunction, length);
}

void Regions::visitMemTransferInst(MemTransferInst &I) {
  assert(currentFunction && "currentFunction must be set during visit");
  unsigned length;

  if (auto CI = dyn_cast<ConstantInt>(I.getLength()))
    length = CI->getZExtValue();
  else
    length = std::numeric_limits<unsigned>::max();

  // We need to visit the source location otherwise
  // extra merges will happen in the translation phase,
  // resulting in ``hanging'' regions.
  idx(I.getSource(), currentFunction, length);
  idx(I.getDest(), currentFunction, length);
}

void Regions::visitCallBase(CallBase &I) {
  assert(currentFunction && "currentFunction must be set during visit");
  Function *F = I.getCalledFunction();
  std::string name = F && F->hasName() ? F->getName().str() : "";

  if (I.getType()->isPointerTy() && name != "malloc")
    idx(&I, currentFunction);

  if (name.find("__SMACK_values") != std::string::npos) {
    assert(I.arg_size() == 2 && "Expected two operands.");
    const Value *P = I.getArgOperand(0);
    const Value *N = I.getArgOperand(1);

    while (isa<const CastInst>(P))
      P = dyn_cast<const CastInst>(P)->getOperand(0);
    const PointerType *T = dyn_cast<PointerType>(P->getType());
    assert(T && "Expected pointer argument.");

    if (auto I = dyn_cast<ConstantInt>(N)) {
      const unsigned bound = I->getZExtValue();
      const unsigned size = T->getElementType()->getIntegerBitWidth() / 8;
      const unsigned length = bound * size;
      idx(P, currentFunction, length);

    } else {
      llvm_unreachable("Non-constant size expression not yet handled.");
    }
  }
}

FunctionRegionInfo Regions::emptyRegionInfo;

namespace {
using NodeSet = std::set<const seadsa::Node *>;

void markReachableNodes(const seadsa::Node *N, NodeSet &nodes) {
  if (!N)
    return;
  if (nodes.insert(N).second) {
    for (auto &link : N->links())
      markReachableNodes(link.second->getNode(), nodes);
  }
}

void reachableInterfaceNodes(const Function *F, seadsa::Graph &G,
                             NodeSet &inputReach, NodeSet &returnReach) {
  for (auto &A : F->args()) {
    if (G.hasCell(A))
      markReachableNodes(G.getCell(A).getNode(), inputReach);
  }

  for (auto &GV : G.globals())
    markReachableNodes(GV.second->getNode(), inputReach);

  if (G.hasRetCell(*F))
    markReachableNodes(G.getRetCell(*F).getNode(), returnReach);
}

std::unique_ptr<seadsa::DsaCallSite> makeDsaCallSite(CallBase *CB,
                                                     Function *callee) {
  auto site =
      std::unique_ptr<seadsa::DsaCallSite>(new seadsa::DsaCallSite(*CB));
  if (site->getCallee() == callee)
    return site;
  return std::unique_ptr<seadsa::DsaCallSite>(
      new seadsa::DsaCallSite(*CB, *callee));
}

void remapRegionSet(std::set<unsigned> &regions, unsigned keep,
                    unsigned remove) {
  std::set<unsigned> remapped;
  for (unsigned r : regions) {
    if (r == remove)
      remapped.insert(keep);
    else
      remapped.insert(r > remove ? r - 1 : r);
  }
  regions = remapped;
}

unsigned remapRegionIndex(unsigned r, unsigned keep, unsigned remove) {
  if (r == remove)
    return keep;
  return r > remove ? r - 1 : r;
}
} // namespace

void Regions::computeCallSiteMappings(Module &M) {
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        Function *callee = CB->getCalledFunction();
        if (!callee)
          callee = dyn_cast<Function>(
              CB->getCalledOperand()->stripPointerCastsAndAliases());
        if (!callee || callee->isDeclaration())
          continue;
        if (callee->hasName() &&
            SmackOptions::usesGlobalMemory(callee->getName()))
          continue;

        computeOneCallSiteMapping(CB, &F, callee);
      }
    }
  }
}

void Regions::computeOneCallSiteMapping(CallBase *CI, const Function *caller,
                                        Function *callee) {
  // Build the mapping in place so that any merges triggered by idx() below
  // (which remap all registered call-site mappings) also repair the entries
  // added so far for this call site.
  auto &mapping = callSiteMappings[CI];
  mapping.clear();

  if (!DSA->hasGraph(*callee) || !DSA->hasGraph(*caller))
    return;

  auto &calleeG = DSA->getGraph(*callee);
  auto &callerG = DSA->getGraph(*caller);
  auto dsaCS = makeDsaCallSite(CI, callee);

  seadsa::SimulationMapper simMap;
  bool mapped = seadsa::Graph::computeCalleeCallerMapping(*dsaCS, calleeG,
                                                          callerG, simMap);
  if (!mapped)
    report_fatal_error(
        "SeaDsa failed to map callee regions to caller regions.");

  // Iterate by index over the live callee region vector: idx() below can
  // merge regions (in the caller, or in the callee itself for recursive
  // calls), which invalidates references and shifts indices. A copy of the
  // current region is taken per iteration; if indices do shift mid-loop,
  // the structural-version check in runOnModule forces another (eventually
  // mutation-free) pass over all call sites.
  for (unsigned i = 0; i < funcRegionVecs[callee].size(); i++) {
    Region calleeRegion = funcRegionVecs[callee][i];
    auto *rep = calleeRegion.getRepresentative();
    if (!rep)
      continue;

    seadsa::Cell calleeCell(const_cast<seadsa::Node *>(rep),
                            calleeRegion.getOffset());
    seadsa::Cell callerCell = simMap.get(calleeCell);
    if (callerCell.isNull())
      continue;

    Region callerRegion(callerCell.getNode(), callerCell.getOffset(),
                        std::max(calleeRegion.getLength(), 1u),
                        calleeRegion.getType(), calleeRegion.bytewiseAccess(),
                        caller->getContext());
    mapping[i] = idx(callerRegion, caller);
  }
}

bool Regions::mergeCalleeRegion(const Function *F, unsigned keep,
                                unsigned remove) {
  if (keep == remove)
    return false;
  // Ensure keep < remove for consistent processing.
  if (keep > remove)
    std::swap(keep, remove);

  auto &regions = funcRegionVecs[F];
  if (remove >= regions.size())
    return false;

  Region removedRegion = regions[remove];

  // Merge region data.
  regions[keep].merge(regions[remove]);
  regions.erase(regions.begin() + remove);

  remapAfterMerge(F, keep, remove);

  // Record the removed region so later probes that only overlap it (e.g.,
  // when its representative differs from the canonical region's) still
  // resolve to the merged index.
  mergedRegionAliases[F].push_back({removedRegion, keep});

  return true;
}

void Regions::remapAfterMerge(const Function *F, unsigned keep,
                              unsigned remove) {
  structuralVersion++;

  auto &aliases = mergedRegionAliases[F];
  for (auto &alias : aliases)
    alias.second = remapRegionIndex(alias.second, keep, remove);

  // Shift indices in FunctionRegionInfo.
  auto &info = funcRegions[F];
  remapRegionSet(info.readRegions, keep, remove);
  remapRegionSet(info.modifiedRegions, keep, remove);
  remapRegionSet(info.inputRegions, keep, remove);
  remapRegionSet(info.outputRegions, keep, remove);

  // Shift indices in global-memory mappings: keys are F-local indices, and
  // values are entry-function indices.
  {
    auto it = globalMemoryMappings.find(F);
    if (it != globalMemoryMappings.end()) {
      std::map<unsigned, unsigned> newMapping;
      for (auto &m : it->second)
        newMapping[remapRegionIndex(m.first, keep, remove)] = m.second;
      it->second = newMapping;
    }
    if (F->hasName() && SmackOptions::isEntryPoint(F->getName()))
      for (auto &gm : globalMemoryMappings)
        for (auto &m : gm.second)
          m.second = remapRegionIndex(m.second, keep, remove);
  }

  // Shift F-local indices in the shared-region table.
  {
    std::map<std::pair<const Function *, unsigned>, unsigned> newIndex;
    for (auto &m : sharedRegionIndex) {
      auto key = m.first;
      if (key.first == F)
        key.second = remapRegionIndex(key.second, keep, remove);
      newIndex.insert({key, m.second});
    }
    sharedRegionIndex = newIndex;
  }

  // Update all call-site mappings that reference F.
  // Mappings are callee_idx -> caller_idx; a self-recursive call site has F
  // on both sides and needs both its keys and its values shifted.
  for (auto &csEntry : callSiteMappings) {
    auto *CB = const_cast<CallBase *>(csEntry.first);
    auto &mapping = csEntry.second;

    // Determine if F is the callee and/or the caller of this call site.
    Function *csCallee = CB->getCalledFunction();
    if (!csCallee)
      csCallee = dyn_cast<Function>(
          CB->getCalledOperand()->stripPointerCastsAndAliases());
    const Function *csCaller = CB->getParent()->getParent();

    if (csCallee != F && csCaller != F)
      continue;

    // When the `remove` key collapses into `keep`, prefer the existing
    // `keep` entry (typically from parameter mapping, which is
    // call-site-specific and more precise than globals).
    std::map<unsigned, unsigned> newMapping;
    for (auto &m : mapping) {
      unsigned k = m.first;
      unsigned v = m.second;
      if (csCallee == F)
        k = remapRegionIndex(k, keep, remove);
      if (csCaller == F)
        v = remapRegionIndex(v, keep, remove);
      auto ins = newMapping.insert({k, v});
      // Dropping a colliding entry whose caller region differs loses the
      // association between the merged callee region and that caller
      // region. During Phase 3 the next pass recomputes the mapping; after
      // Phase 3 (propagateRegionMerges) it is not recomputed, so count the
      // loss and report it once instead of failing silently.
      if (!ins.second && ins.first->second != v && mappingsFinal) {
        droppedMappings++;
        SDEBUG(errs() << "[regions] dropped call-site mapping " << remove
                      << " -> " << v << " (kept " << keep << " -> "
                      << ins.first->second << ") merging regions of "
                      << F->getName() << "\n");
      }
    }
    mapping = newMapping;
  }
}

void Regions::propagateRegionMerges(Module &M) {
  // Build call graph: caller -> [(CallBase, callee)]
  std::map<const Function *, std::vector<std::pair<CallBase *, Function *>>>
      callGraph;
  // Reverse call graph: callee -> [caller]
  std::map<const Function *, std::set<const Function *>> callers;

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        Function *callee = CB->getCalledFunction();
        if (!callee)
          callee = dyn_cast<Function>(
              CB->getCalledOperand()->stripPointerCastsAndAliases());
        if (!callee || callee->isDeclaration())
          continue;
        if (callee->hasName() &&
            SmackOptions::usesGlobalMemory(callee->getName()))
          continue;
        callGraph[&F].push_back({CB, callee});
        callers[callee].insert(&F);
      }
    }
  }

  // Compute SCCs using Tarjan's algorithm.
  std::map<const Function *, int> index, lowlink;
  std::map<const Function *, bool> onStack;
  std::vector<const Function *> stack;
  std::vector<std::vector<const Function *>> sccs;
  int idx = 0;

  std::function<void(const Function *)> strongconnect = [&](const Function *F) {
    index[F] = lowlink[F] = idx++;
    stack.push_back(F);
    onStack[F] = true;

    if (callGraph.count(F)) {
      for (auto &edge : callGraph[F]) {
        Function *callee = edge.second;
        if (!index.count(callee)) {
          strongconnect(callee);
          lowlink[F] = std::min(lowlink[F], lowlink[callee]);
        } else if (onStack[callee]) {
          lowlink[F] = std::min(lowlink[F], index[callee]);
        }
      }
    }

    if (lowlink[F] == index[F]) {
      std::vector<const Function *> scc;
      const Function *w;
      do {
        w = stack.back();
        stack.pop_back();
        onStack[w] = false;
        scc.push_back(w);
      } while (w != F);
      sccs.push_back(scc);
    }
  };

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (!index.count(&F))
      strongconnect(&F);
  }

  // SCCs are in reverse topological order (callees before callers).
  // Reverse to get callers before callees (top-down).
  std::reverse(sccs.begin(), sccs.end());

  bool globalChanged = true;
  while (globalChanged) {
    globalChanged = false;

    // Top-down pass: merge callee regions when multiple map to same caller
    // region.
    for (auto &scc : sccs) {
      bool changed = true;
      while (changed) {
        changed = false;
        for (const Function *F : scc) {
          if (!callGraph.count(F))
            continue;
          for (auto &edge : callGraph[F]) {
            CallBase *CB = edge.first;
            Function *callee = edge.second;
            if (!callSiteMappings.count(CB))
              continue;

            auto &mapping = callSiteMappings[CB];

            // Check for collisions: multiple callee regions -> same caller
            // region.
            std::map<unsigned, std::vector<unsigned>> callerToCallees;
            for (auto &m : mapping)
              callerToCallees[m.second].push_back(m.first);

            for (auto &entry : callerToCallees) {
              auto &calleeIndices = entry.second;
              if (calleeIndices.size() <= 1)
                continue;

              // Merge all colliding callee regions into the first.
              std::sort(calleeIndices.begin(), calleeIndices.end());
              // Merge from highest index down to avoid shifting issues.
              for (int i = calleeIndices.size() - 1; i >= 1; i--) {
                unsigned keep = calleeIndices[0];
                unsigned remove = calleeIndices[i];
                if (mergeCalleeRegion(callee, keep, remove)) {
                  changed = true;
                }
              }

              // mergeCalleeRegion already updated all call-site mapping
              // indices. Do NOT recompute via computeOneCallSiteMapping —
              // that calls idx() which can recreate the merged-away region
              // (different DSA representative), causing an infinite loop.
              break; // restart collision check since indices shifted
            }
          }
        }
        if (changed)
          globalChanged = true;
      }
    }

    // Bottom-up pass: merge caller regions when the callee has collapsed
    // them. Merging on representative-node equality alone loses field
    // sensitivity (disjoint offset ranges on the same node are merged too),
    // but it is what keeps per-function region counts bounded: the
    // link-following closure creates whole-node regions, and without this
    // consolidation the transitive access closure blows up region counts on
    // large inputs. Field-granular threading needs a redesign of the
    // closure/interface computation, not just a weaker merge condition.
    for (auto it = sccs.rbegin(); it != sccs.rend(); ++it) {
      auto &scc = *it;
      bool changed = true;
      while (changed) {
        changed = false;
        for (const Function *F : scc) {
          if (!callGraph.count(F))
            continue;
          bool merged = false;
          for (auto &edge : callGraph[F]) {
            CallBase *CB = edge.first;
            if (!callSiteMappings.count(CB))
              continue;
            if (!funcRegionVecs.count(F))
              continue;

            auto &mapping = callSiteMappings[CB];
            auto &callerRegions = funcRegionVecs[F];

            // Build rep -> mapped caller region index.
            std::map<const seadsa::Node *, unsigned> repToMappedCaller;
            std::set<unsigned> mappedCallerIndices;
            for (auto &m : mapping) {
              mappedCallerIndices.insert(m.second);
              if (m.second < callerRegions.size()) {
                auto *rep = callerRegions[m.second].getRepresentative();
                if (rep)
                  repToMappedCaller[rep] = m.second;
              }
            }

            // Find unmapped caller regions whose rep matches a mapped one.
            for (unsigned i = 0; i < callerRegions.size() && !merged; i++) {
              if (mappedCallerIndices.count(i))
                continue;
              auto *rep = callerRegions[i].getRepresentative();
              if (rep && repToMappedCaller.count(rep)) {
                unsigned keep = repToMappedCaller[rep];
                if (mergeCalleeRegion(F, keep, i)) {
                  changed = true;
                  merged = true;
                }
              }
            }
            if (merged)
              break; // restart since indices shifted
          }
          if (changed)
            break;
        }
        if (changed)
          globalChanged = true;
      }
    }
  }
}

void Regions::computeGlobalMemoryMappings(Module &M) {
  const Function *entryF = nullptr;
  for (auto &F : M) {
    if (!F.isDeclaration() && F.hasName() &&
        SmackOptions::isEntryPoint(F.getName())) {
      entryF = &F;
      break;
    }
  }
  if (!entryF || !DSA->hasGraph(*entryF))
    return;

  // Map each function's global-backed regions to the entry function's
  // region holding the same global. When one function-level region covers
  // globals that the entry function keeps in separate regions, those entry
  // regions alias through this function and must be merged;
  // mergeCalleeRegion repairs all bookkeeping (including these mappings),
  // and merges strictly decrease the entry region count, so iterating to a
  // fixpoint terminates.
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto &F : M) {
      if (F.isDeclaration() || &F == entryF)
        continue;
      // usesGlobalMemory functions (e.g., __SMACK_static_init) are emitted
      // in the entry function's region context and need no mapping.
      if (F.hasName() && SmackOptions::usesGlobalMemory(F.getName()))
        continue;
      if (!DSA->hasGraph(F))
        continue;
      auto &fGraph = DSA->getGraph(F);
      auto &entryGraph = DSA->getGraph(*entryF);
      // Build in place: entry-side merges triggered below remap the values
      // of every registered mapping, including this one.
      auto &mapping = globalMemoryMappings[&F];
      for (auto &GV : M.globals()) {
        if (!fGraph.hasCell(GV) || !entryGraph.hasCell(GV))
          continue;
        unsigned fR = idx(&GV, &F);
        unsigned entryR = idx(&GV, entryF);
        auto it = mapping.find(fR);
        if (it == mapping.end()) {
          mapping[fR] = entryR;
          changed = true;
        } else if (it->second != entryR) {
          mergeCalleeRegion(entryF, it->second, entryR);
          changed = true;
        }
      }
      // The entry region's declared map type must cover this function's
      // view of the memory (relevant under bit-precise encodings), and the
      // map must be module-level since other functions reference it.
      auto &entryRegions = funcRegionVecs[entryF];
      auto &fRegions = funcRegionVecs[&F];
      for (auto &m : mapping) {
        assert(m.first < fRegions.size() && m.second < entryRegions.size() &&
               "region indices must be repaired by remapAfterMerge");
        entryRegions[m.second].mergeAttributes(fRegions[m.first]);
        entryRegions[m.second].markGlobalScope();
      }
    }
  }
}

void Regions::unifySharedRegions(Module &M) {
  const Function *entryF = nullptr;
  for (auto &F : M) {
    if (!F.isDeclaration() && F.hasName() &&
        SmackOptions::isEntryPoint(F.getName())) {
      entryF = &F;
      break;
    }
  }

  // Union-find over (function, region index) pairs, linked by call-site
  // mappings and global-memory mappings. Rebuilt from scratch whenever an
  // entry-side merge shifts indices (mergeCalleeRegion repairs the
  // mappings the union-find is derived from, so rebuilding is correct).
  while (true) {
    std::map<std::pair<const Function *, unsigned>, unsigned> ids;
    std::vector<unsigned> parent;
    auto id = [&](const Function *F, unsigned r) {
      auto key = std::make_pair(F, r);
      auto it = ids.find(key);
      if (it != ids.end())
        return it->second;
      unsigned n = parent.size();
      ids[key] = n;
      parent.push_back(n);
      return n;
    };
    std::function<unsigned(unsigned)> find = [&](unsigned x) {
      while (parent[x] != x) {
        parent[x] = parent[parent[x]];
        x = parent[x];
      }
      return x;
    };
    auto unite = [&](unsigned a, unsigned b) { parent[find(a)] = find(b); };

    for (auto &cs : callSiteMappings) {
      auto *CB = const_cast<CallBase *>(cs.first);
      Function *callee = CB->getCalledFunction();
      if (!callee)
        callee = dyn_cast<Function>(
            CB->getCalledOperand()->stripPointerCastsAndAliases());
      if (!callee)
        continue;
      const Function *caller = CB->getParent()->getParent();
      for (auto &m : cs.second)
        unite(id(callee, m.first), id(caller, m.second));
    }
    if (entryF)
      for (auto &gm : globalMemoryMappings)
        for (auto &m : gm.second)
          unite(id(gm.first, m.first), id(entryF, m.second));

    // A class containing two entry regions means those regions alias
    // through some call chain; merge them and rebuild.
    bool merged = false;
    if (entryF) {
      std::map<unsigned, unsigned> entryRep;
      for (auto &kv : ids) {
        if (kv.first.first != entryF)
          continue;
        unsigned root = find(kv.second);
        auto it = entryRep.find(root);
        if (it == entryRep.end())
          entryRep[root] = kv.first.second;
        else if (it->second != kv.first.second) {
          mergeCalleeRegion(entryF, it->second, kv.first.second);
          merged = true;
          break;
        }
      }
    }
    if (merged)
      continue;

    // Stable: bind every non-entry member of an entry class to the entry
    // region, and give every entry-less multi-member class a fresh
    // module-level shared map.
    std::map<unsigned, unsigned> classEntry;
    if (entryF)
      for (auto &kv : ids)
        if (kv.first.first == entryF)
          classEntry[find(kv.second)] = kv.first.second;

    std::map<unsigned, unsigned> classSize;
    for (auto &kv : ids)
      classSize[find(kv.second)]++;

    std::map<unsigned, unsigned> classShared;
    for (auto &kv : ids) {
      const Function *F = kv.first.first;
      unsigned r = kv.first.second;
      if (F == entryF)
        continue;
      assert(r < funcRegionVecs[F].size() &&
             "region indices must be repaired by remapAfterMerge");
      unsigned root = find(kv.second);
      auto ce = classEntry.find(root);
      if (ce != classEntry.end()) {
        globalMemoryMappings[F][r] = ce->second;
        assert(ce->second < funcRegionVecs[entryF].size() &&
               "region indices must be repaired by remapAfterMerge");
        funcRegionVecs[entryF][ce->second].mergeAttributes(
            funcRegionVecs[F][r]);
        // Referenced from other functions: must be a module-level map,
        // not a local of the entry procedure.
        funcRegionVecs[entryF][ce->second].markGlobalScope();
        continue;
      }
      if (classSize[root] < 2)
        continue; // function-private: stays a procedure-local map
      auto cs = classShared.find(root);
      unsigned s;
      if (cs == classShared.end()) {
        s = sharedRegions.size();
        sharedRegions.push_back(funcRegionVecs[F][r]);
        classShared[root] = s;
      } else {
        s = cs->second;
        sharedRegions[s].mergeAttributes(funcRegionVecs[F][r]);
      }
      sharedRegionIndex[{F, r}] = s;
    }
    break;
  }
}

void Regions::computeFunctionRegions(Module &M) {
  // Transitive closure: propagate callee region accesses to callers
  // through call-site mappings.
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      FunctionRegionInfo &info = funcRegions[&F];
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;
          Function *callee = CB->getCalledFunction();
          if (!callee)
            callee = dyn_cast<Function>(
                CB->getCalledOperand()->stripPointerCastsAndAliases());
          if (!callee || callee->isDeclaration())
            continue;
          if (!callSiteMappings.count(CB))
            continue;

          auto &mapping = callSiteMappings[CB];
          auto &calleeInfo = funcRegions[callee];

          for (unsigned calleeR : calleeInfo.readRegions) {
            if (mapping.count(calleeR)) {
              if (info.readRegions.insert(mapping.at(calleeR)).second)
                changed = true;
            }
          }
          for (unsigned calleeR : calleeInfo.modifiedRegions) {
            if (mapping.count(calleeR)) {
              if (info.modifiedRegions.insert(mapping.at(calleeR)).second)
                changed = true;
            }
          }
        }
      }
    }
  }
}

void Regions::computeInterfaceRegions(Module &M) {
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;

    auto &info = funcRegions[&F];
    info.inputRegions.clear();
    info.outputRegions.clear();

    if (!DSA->hasGraph(F))
      continue;

    NodeSet inputReach, returnReach;
    auto &graph = DSA->getGraph(F);
    reachableInterfaceNodes(&F, graph, inputReach, returnReach);

    // Regions mapped to module-level maps (entry or shared) are accessed
    // directly and are not threaded through the procedure signature.
    auto gmIt = globalMemoryMappings.find(&F);
    const std::map<unsigned, unsigned> *gm =
        gmIt != globalMemoryMappings.end() ? &gmIt->second : nullptr;

    auto accessed = getAccessedRegions(&F);
    for (unsigned r : accessed) {
      if ((gm && gm->count(r)) || sharedRegionIndex.count({&F, r}))
        continue;
      auto *rep = funcRegionVecs[&F][r].getRepresentative();
      if (rep && inputReach.count(rep))
        info.inputRegions.insert(r);
    }

    for (unsigned r : info.modifiedRegions) {
      if ((gm && gm->count(r)) || sharedRegionIndex.count({&F, r}))
        continue;
      auto *rep = funcRegionVecs[&F][r].getRepresentative();
      if (rep && (inputReach.count(rep) || returnReach.count(rep)))
        info.outputRegions.insert(r);
    }
  }
}

const FunctionRegionInfo &
Regions::getFunctionRegionInfo(const Function *F) const {
  auto it = funcRegions.find(F);
  if (it != funcRegions.end())
    return it->second;
  return emptyRegionInfo;
}

std::set<unsigned> Regions::getAccessedRegions(const Function *F) const {
  auto &info = getFunctionRegionInfo(F);
  std::set<unsigned> result = info.readRegions;
  result.insert(info.modifiedRegions.begin(), info.modifiedRegions.end());
  return result;
}

const std::map<unsigned, unsigned> &
Regions::getCallSiteMapping(const CallBase *CB) const {
  static const std::map<unsigned, unsigned> emptyMapping;
  auto it = callSiteMappings.find(CB);
  if (it != callSiteMappings.end())
    return it->second;
  return emptyMapping;
}

const std::map<unsigned, unsigned> &
Regions::getGlobalMemoryMapping(const Function *F) const {
  static const std::map<unsigned, unsigned> emptyMapping;
  auto it = globalMemoryMappings.find(F);
  if (it != globalMemoryMappings.end())
    return it->second;
  return emptyMapping;
}

int Regions::getSharedRegionIndex(const Function *F, unsigned r) const {
  auto it = sharedRegionIndex.find({F, r});
  if (it != sharedRegionIndex.end())
    return (int)it->second;
  return -1;
}

} // namespace smack
