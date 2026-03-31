//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/Regions.h"
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "smack/SmackOptions.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"

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
  this->length = length;

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

Region::Region(const seadsa::Node *node, LLVMContext &ctx) {
  context = &ctx;
  representative = node;
  type = nullptr;
  offset = 0;
  length = node ? node->size() : std::numeric_limits<unsigned>::max();
  singleton = false;
  allocated = !representative || isAllocated(representative);
  bytewise = true;
  incomplete = !representative || representative->isIncomplete();
  complicated = !representative || isComplicated(representative);
  collapsed = !representative || representative->isOffsetCollapsed();
  globalScope = !representative || DSA->getNumGlobals(representative) > 0;
}

bool Region::isDisjoint(unsigned offset, unsigned length) {
  return this->offset + this->length <= offset ||
         offset + length <= this->offset;
}

void Region::merge(Region &R) {
  bool collapse = type != R.type;
  unsigned long low = std::min(offset, R.offset);
  unsigned long high = std::max(offset + length, R.offset + R.length);
  offset = low;
  length = high - low;
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
          if (auto *CI = dyn_cast<CallInst>(&I)) {
            for (unsigned i = 0; i < CI->getNumArgOperands(); i++) {
              Value *arg = CI->getArgOperand(i);
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
        for (unsigned i = 0; i < origSize; i++) {
          auto *rep = regions[i].getRepresentative();
          if (!rep)
            continue;
          for (auto &link : rep->links()) {
            auto *target = link.second->getNode();
            if (target && !existing.count(target)) {
              existing.insert(target);
              Region R(target, F.getContext());
              idx(R, &F);
              grew = true;
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

    // Phase 2.5: Compute global-memory mappings for non-entry usesGlobalMemory
    // functions (e.g., __SMACK_static_init) to the entry function's indices.
    computeGlobalMemoryMappings(M);

    // Phase 3: Compute call-site mappings (callee region -> caller region).
    // Iterate because link-following may create new regions in callers,
    // which then need mappings computed for their own callers.
    for (int iter = 0; iter < 10; iter++) {
      unsigned prevTotal = 0;
      for (auto &kv : funcRegionVecs)
        prevTotal += kv.second.size();
      computeCallSiteMappings(M);
      unsigned newTotal = 0;
      for (auto &kv : funcRegionVecs)
        newTotal += kv.second.size();
      if (newTotal == prevTotal)
        break;
    }

    // Phase 3.5: Propagate region merges top-down through the call graph.
    // When a caller collapses two callee regions (maps both to the same
    // caller region), the callee must merge them to preserve the invariant
    // that regions never alias.
    propagateRegionMerges(M);

    // Phase 4: Transitive closure of region access sets.
    computeFunctionRegions(M);
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

  for (r = 0; r < regions.size(); ++r) {
    if (regions[r].overlaps(R)) {

      SDEBUG(errs() << "[regions]   found overlap at index " << r << ": ");
      SDEBUG(regions[r].print(errs()));
      SDEBUG(errs() << "\n");

      regions[r].merge(R);

      SDEBUG(errs() << "[regions]   merged region: ");
      SDEBUG(regions[r].print(errs()));
      SDEBUG(errs() << "\n");

      break;
    }
  }

  if (r == regions.size())
    regions.emplace_back(R);

  else {
    // In case R was merged with an existing region, we must now also merge
    // any other region which intersects with R.
    unsigned q = r + 1;
    while (q < regions.size()) {
      if (regions[r].overlaps(regions[q])) {

        SDEBUG(errs() << "[regions]   found extra overlap at index " << q
                      << ": ");
        SDEBUG(regions[q].print(errs()));
        SDEBUG(errs() << "\n");

        regions[r].merge(regions[q]);
        regions.erase(regions.begin() + q);

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

void Regions::visitCallInst(CallInst &I) {
  assert(currentFunction && "currentFunction must be set during visit");
  Function *F = I.getCalledFunction();
  std::string name = F && F->hasName() ? F->getName().str() : "";

  if (I.getType()->isPointerTy() && name != "malloc")
    idx(&I, currentFunction);

  if (name.find("__SMACK_values") != std::string::npos) {
    assert(I.getNumArgOperands() == 2 && "Expected two operands.");
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

void Regions::computeCallSiteMappings(Module &M) {
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = dyn_cast<CallInst>(&I);
        if (!CI)
          continue;
        Function *callee = CI->getCalledFunction();
        if (!callee)
          callee = dyn_cast<Function>(
              CI->getCalledOperand()->stripPointerCastsAndAliases());
        if (!callee || callee->isDeclaration())
          continue;
        if (callee->hasName() &&
            SmackOptions::usesGlobalMemory(callee->getName()))
          continue;

        computeOneCallSiteMapping(CI, &F, callee);
      }
    }
  }
}

void Regions::computeOneCallSiteMapping(CallInst *CI, const Function *caller,
                                        Function *callee) {
  std::map<unsigned, unsigned> mapping;

  // Map via actual/formal pointer parameter pairs.
  unsigned argIdx = 0;
  for (auto &formalArg : callee->args()) {
    if (argIdx < CI->getNumArgOperands() &&
        formalArg.getType()->isPointerTy()) {
      Value *actualArg = CI->getArgOperand(argIdx);
      unsigned calleeR = idx(&formalArg, callee);
      unsigned callerR = idx(actualArg, caller);
      mapping[calleeR] = callerR;
    }
    argIdx++;
  }

  // Map via return value: if the callee returns a pointer, map the
  // callee's return value region to the caller's region for the call result.
  if (CI->getType()->isPointerTy() && !callee->getReturnType()->isVoidTy()) {
    // Find a return instruction in the callee to get the return value.
    for (auto &BB : *callee) {
      if (auto *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
        if (RI->getReturnValue() &&
            RI->getReturnValue()->getType()->isPointerTy()) {
          unsigned calleeR = idx(RI->getReturnValue(), callee);
          unsigned callerR = idx(CI, caller);
          if (!mapping.count(calleeR))
            mapping[calleeR] = callerR;
          break;
        }
      }
    }
  }

  // Map via globals accessed by callee.
  Module *M = CI->getModule();
  for (auto &GV : M->globals()) {
    if (!GV.getType()->isPointerTy())
      continue;
    // Only map if callee's graph has a cell for this global.
    if (!DSA->hasGraph(*callee))
      continue;
    auto &calleeG = DSA->getGraph(*callee);
    if (!calleeG.hasCell(GV))
      continue;
    if (!DSA->hasGraph(*caller))
      continue;
    auto &callerG = DSA->getGraph(*caller);
    if (!callerG.hasCell(GV))
      continue;

    unsigned calleeR = idx(&GV, callee);
    unsigned callerR = idx(&GV, caller);
    // Don't overwrite parameter mapping — it's call-site-specific
    // and more precise than the global mapping.
    if (!mapping.count(calleeR))
      mapping[calleeR] = callerR;
  }

  // Extend mapping: for any unmapped callee region whose representative
  // matches a mapped callee region's representative, map it to the same
  // caller region. This handles cases like p[-1] where the callee accesses
  // a different offset of the same DSA node as the parameter.
  if (funcRegionVecs.count(callee)) {
    auto &calleeRegions = funcRegionVecs[callee];
    // Build rep -> caller region from existing mapping.
    std::map<const seadsa::Node *, unsigned> repToCallerRegion;
    for (auto &entry : mapping) {
      unsigned calleeIdx = entry.first;
      unsigned callerIdx = entry.second;
      if (calleeIdx < calleeRegions.size()) {
        auto *rep = calleeRegions[calleeIdx].getRepresentative();
        if (rep)
          repToCallerRegion[rep] = callerIdx;
      }
    }
    // Map unmapped callee regions with matching representatives.
    for (unsigned i = 0; i < calleeRegions.size(); i++) {
      if (mapping.count(i))
        continue;
      auto *rep = calleeRegions[i].getRepresentative();
      if (rep && repToCallerRegion.count(rep))
        mapping[i] = repToCallerRegion[rep];
    }
  }

  // Extend mapping via DSA link following: discover node correspondences
  // by traversing pointer edges in DSA graphs. This handles heap structures
  // reachable through globals/parameters (e.g., global head -> list struct).
  if (funcRegionVecs.count(callee) && funcRegionVecs.count(caller) &&
      DSA->hasGraph(*callee) && DSA->hasGraph(*caller)) {
    auto &calleeRegions = funcRegionVecs[callee];
    auto &callerRegions = funcRegionVecs[caller];

    // Build node-to-node mapping from existing region mapping.
    // Only use non-conflicting entries (same callee node -> same caller node).
    std::map<const seadsa::Node *, const seadsa::Node *> calleeToCallerNode;
    std::set<const seadsa::Node *> conflicting;
    for (auto &entry : mapping) {
      unsigned calleeIdx = entry.first;
      unsigned callerIdx = entry.second;
      if (calleeIdx < calleeRegions.size() &&
          callerIdx < callerRegions.size()) {
        auto *ce = calleeRegions[calleeIdx].getRepresentative();
        auto *cr = callerRegions[callerIdx].getRepresentative();
        if (ce && cr) {
          auto it = calleeToCallerNode.find(ce);
          if (it != calleeToCallerNode.end() && it->second != cr)
            conflicting.insert(ce);
          else
            calleeToCallerNode[ce] = cr;
        }
      }
    }
    for (auto *n : conflicting)
      calleeToCallerNode.erase(n);

    // Follow pointer links to discover additional node correspondences.
    bool extended = true;
    while (extended) {
      extended = false;
      for (auto &nodeEntry : calleeToCallerNode) {
        auto *calleeNode = nodeEntry.first;
        auto *callerNode = nodeEntry.second;
        for (auto &link : calleeNode->links()) {
          auto &field = link.first;
          auto *calleeTarget = link.second->getNode();
          if (!calleeTarget || calleeToCallerNode.count(calleeTarget) ||
              conflicting.count(calleeTarget))
            continue;
          if (callerNode->hasLink(field)) {
            auto *callerTarget = callerNode->getLink(field).getNode();
            if (callerTarget) {
              calleeToCallerNode[calleeTarget] = callerTarget;
              extended = true;
            }
          }
        }
      }
    }

    // Map remaining unmapped callee regions via discovered correspondences.
    // First try to find an existing caller region; if none, create one.
    for (unsigned i = 0; i < calleeRegions.size(); i++) {
      if (mapping.count(i))
        continue;
      auto *rep = calleeRegions[i].getRepresentative();
      if (!rep || conflicting.count(rep))
        continue;
      auto nodeIt = calleeToCallerNode.find(rep);
      const seadsa::Node *callerNode =
          (nodeIt != calleeToCallerNode.end()) ? nodeIt->second : nullptr;
      if (!callerNode)
        continue;
      // Find existing caller region for this node.
      bool found = false;
      for (unsigned j = 0; j < callerRegions.size(); j++) {
        if (callerRegions[j].getRepresentative() == callerNode) {
          mapping[i] = j;
          found = true;
          break;
        }
      }
      if (!found) {
        // Create a caller region for this node.
        Region R(callerNode, caller->getContext());
        mapping[i] = idx(R, caller);
        // Re-fetch since idx may have modified the vector.
        callerRegions = funcRegionVecs[caller];
      }
    }
  }

  callSiteMappings[CI] = mapping;
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

  // Merge region data.
  regions[keep].merge(regions[remove]);
  regions.erase(regions.begin() + remove);

  // Shift indices in FunctionRegionInfo.
  auto &info = funcRegions[F];
  std::set<unsigned> newRead, newMod;
  for (unsigned r : info.readRegions) {
    if (r == remove)
      newRead.insert(keep);
    else
      newRead.insert(r > remove ? r - 1 : r);
  }
  for (unsigned r : info.modifiedRegions) {
    if (r == remove)
      newMod.insert(keep);
    else
      newMod.insert(r > remove ? r - 1 : r);
  }
  info.readRegions = newRead;
  info.modifiedRegions = newMod;

  // Update all call-site mappings that reference F.
  // Mappings are callee_idx -> caller_idx.
  for (auto &csEntry : callSiteMappings) {
    CallInst *CI = const_cast<CallInst *>(csEntry.first);
    auto &mapping = csEntry.second;

    // Determine if F is the callee or the caller of this call site.
    Function *csCallee = CI->getCalledFunction();
    if (!csCallee)
      csCallee = dyn_cast<Function>(
          CI->getCalledOperand()->stripPointerCastsAndAliases());
    const Function *csCaller = CI->getParent()->getParent();

    if (csCallee == F) {
      // F is the callee: shift callee-side (keys) of the mapping.
      // When the `remove` key collapses into `keep`, prefer the
      // existing `keep` entry (typically from parameter mapping,
      // which is call-site-specific and more precise than globals).
      std::map<unsigned, unsigned> newMapping;
      for (auto &m : mapping) {
        unsigned k = m.first;
        if (k == remove)
          k = keep;
        else if (k > remove)
          k--;
        if (!newMapping.count(k))
          newMapping[k] = m.second;
      }
      mapping = newMapping;
    } else if (csCaller == F) {
      // F is the caller: shift caller-side (values) of the mapping.
      std::map<unsigned, unsigned> newMapping;
      for (auto &m : mapping) {
        unsigned v = m.second;
        if (v == remove)
          v = keep;
        else if (v > remove)
          v--;
        newMapping[m.first] = v;
      }
      mapping = newMapping;
    }
  }

  return true;
}

void Regions::propagateRegionMerges(Module &M) {
  // Build call graph: caller -> [(CallInst, callee)]
  std::map<const Function *, std::vector<std::pair<CallInst *, Function *>>>
      callGraph;
  // Reverse call graph: callee -> [caller]
  std::map<const Function *, std::set<const Function *>> callers;

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = dyn_cast<CallInst>(&I);
        if (!CI)
          continue;
        Function *callee = CI->getCalledFunction();
        if (!callee)
          callee = dyn_cast<Function>(
              CI->getCalledOperand()->stripPointerCastsAndAliases());
        if (!callee || callee->isDeclaration())
          continue;
        if (callee->hasName() &&
            SmackOptions::usesGlobalMemory(callee->getName()))
          continue;
        callGraph[&F].push_back({CI, callee});
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
            CallInst *CI = edge.first;
            Function *callee = edge.second;
            if (!callSiteMappings.count(CI))
              continue;

            auto &mapping = callSiteMappings[CI];

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
    // them.
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
            CallInst *CI = edge.first;
            if (!callSiteMappings.count(CI))
              continue;
            if (!funcRegionVecs.count(F))
              continue;

            auto &mapping = callSiteMappings[CI];
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
    if (F.hasName() && SmackOptions::isEntryPoint(F.getName())) {
      entryF = &F;
      break;
    }
  }
  if (!entryF)
    return;

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (!F.hasName())
      continue;
    if (!SmackOptions::usesGlobalMemory(F.getName()))
      continue;
    if (SmackOptions::isEntryPoint(F.getName()))
      continue;

    std::map<unsigned, unsigned> mapping;
    for (auto &GV : M.globals()) {
      if (!GV.getType()->isPointerTy())
        continue;
      if (!DSA->hasGraph(F) || !DSA->hasGraph(*entryF))
        continue;
      auto &fGraph = DSA->getGraph(F);
      auto &entryGraph = DSA->getGraph(*entryF);
      if (!fGraph.hasCell(GV) || !entryGraph.hasCell(GV))
        continue;
      unsigned fR = idx(&GV, &F);
      unsigned entryR = idx(&GV, entryF);
      mapping[fR] = entryR;
    }
    globalMemoryMappings[&F] = mapping;
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
          auto *CI = dyn_cast<CallInst>(&I);
          if (!CI)
            continue;
          Function *callee = CI->getCalledFunction();
          if (!callee)
            callee = dyn_cast<Function>(
                CI->getCalledOperand()->stripPointerCastsAndAliases());
          if (!callee || callee->isDeclaration())
            continue;
          if (!callSiteMappings.count(CI))
            continue;

          auto &mapping = callSiteMappings[CI];
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
Regions::getCallSiteMapping(const CallInst *CI) const {
  static const std::map<unsigned, unsigned> emptyMapping;
  auto it = callSiteMappings.find(CI);
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

} // namespace smack
