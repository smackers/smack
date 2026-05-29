//
// This file is distributed under the MIT License. See LICENSE for details.
//
// SVF-backed DSAWrapper. See include/smack/DSAWrapper.h for the design.
//
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "smack/InitializePasses.h"
#include "smack/SmackOptions.h"
#include <cstdlib>
#include <map>
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Operator.h"
#include "llvm/Analysis/ValueTracking.h"

#include "MemoryModel/PointsTo.h"
#include "SVF-LLVM/LLVMModule.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "SVFIR/SVFVariables.h"
#include "Util/SVFUtil.h"
#include "WPA/Andersen.h"

#define DEBUG_TYPE "smack-dsa-wrapper"

namespace smack {

using namespace llvm;

// SVF is built ONCE into these process-global handles and reused across
// DSAWrapper re-runs AND by the SVF-based devirtualizer: SVF cannot be rebuilt
// in-process (release()+rebuild trips SVFIRBuilder::initialiseNodes' node/sym
// count assert — its many singletons do not fully reset). Kept at file scope (not
// function-local statics) so DSAWrapper::cachedSVF can hand them to the devirt
// pass, which runs after DSAWrapper and must reuse the same pre-devirt points-to.
static SVF::LLVMModuleSet *g_svfModuleSet = nullptr;
static SVF::SVFIR *g_svfIR = nullptr;
static SVF::Andersen *g_svfAndersen = nullptr;

unsigned DSAWrapper::ufFind(unsigned x) {
  auto it = ufParent.find(x);
  if (it == ufParent.end()) {
    ufParent[x] = x;
    return x;
  }
  while (ufParent[x] != x) {
    ufParent[x] = ufParent[ufParent[x]];
    x = ufParent[x];
  }
  return x;
}

void DSAWrapper::ufUnite(unsigned a, unsigned b) {
  ufParent.emplace(a, a);
  ufParent.emplace(b, b);
  unsigned ra = ufFind(a), rb = ufFind(b);
  if (ra != rb)
    ufParent[ra] = rb;
}

void DSAWrapper::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  // We run SVF directly inside runOnModule; no LLVM analysis dependency.
  AU.setPreservesAll();
}

// Underlying object of `v`, additionally seeing through a single-store,
// non-address-escaping alloca "spill slot" — the -O0 lowering
//   %slot = alloca ptr;  store %p, %slot;  ...;  %r = load %slot
// that llvm::getUnderlyingObject stops at (it bottoms out at the load). Such a
// slot is a must-alias equality cell: with EXACTLY ONE pointer store into it and
// no use that escapes its address, every `load %slot` provably yields the stored
// value, so the reload aliases exactly what the stored value aliases. This is
// what reconnects `ctx->field` (lowered to gep(gep(load %ctx.spill))) to the ctx
// param, the dominant cause of the unresolved (C2) region-0 pointers. Bounded
// depth guards pathological chains. SOUND for region merging — it only
// establishes a provable must-alias (merge-only, never removes an alias).
static const llvm::Value *underlyingThroughSpill(const llvm::Value *v,
                                                 unsigned depth = 2) {
  const llvm::Value *base = llvm::getUnderlyingObject(v);
  if (depth == 0)
    return base;
  auto *load = llvm::dyn_cast<llvm::LoadInst>(base);
  if (!load || load->isVolatile())
    return base;
  auto *slot = llvm::dyn_cast<llvm::AllocaInst>(load->getPointerOperand());
  if (!slot)
    return base; // not a direct load from an alloca
  const llvm::StoreInst *theStore = nullptr;
  for (const llvm::User *u : slot->users()) {
    if (auto *st = llvm::dyn_cast<llvm::StoreInst>(u)) {
      // Must store INTO the slot a pointer value; the slot's address must not be
      // the stored value (that would escape it), and there must be only one.
      if (st->getPointerOperand() != slot || st->isVolatile() ||
          !st->getValueOperand()->getType()->isPointerTy())
        return base;
      if (theStore)
        return base; // >1 store ⇒ not a single-valued spill slot
      theStore = st;
    } else if (auto *ld = llvm::dyn_cast<llvm::LoadInst>(u)) {
      if (ld->getPointerOperand() != slot)
        return base;
    } else if (auto *ii = llvm::dyn_cast<llvm::IntrinsicInst>(u)) {
      switch (ii->getIntrinsicID()) {
      case llvm::Intrinsic::dbg_declare:
      case llvm::Intrinsic::dbg_value:
      case llvm::Intrinsic::lifetime_start:
      case llvm::Intrinsic::lifetime_end:
        break; // benign: do not escape the slot address
      default:
        return base;
      }
    } else {
      return base; // any other use escapes the slot address ⇒ unsafe
    }
  }
  if (!theStore)
    return base;
  return underlyingThroughSpill(theStore->getValueOperand(), depth - 1);
}

// True if `p` walks (through casts/GEPs) to a read-only constant global — benign
// constant data that cannot carry a secret, so an unresolved access to it is not
// a soundness concern.
static bool isRoConstData(const llvm::Value *p) {
  const llvm::Value *s = p->stripPointerCasts();
  while (true) {
    if (auto *g = llvm::dyn_cast<llvm::GlobalVariable>(s))
      return g->isConstant();
    if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(s))
      if (ce->getOpcode() == llvm::Instruction::GetElementPtr) {
        s = ce->getOperand(0)->stripPointerCasts();
        continue;
      }
    if (auto *gep = llvm::dyn_cast<llvm::GEPOperator>(s)) {
      s = gep->getPointerOperand()->stripPointerCasts();
      continue;
    }
    return false;
  }
}

void DSAWrapper::computeReachable(llvm::Module &M) {
  reachableFuncs.clear();
  std::vector<llvm::Function *> work;
  for (llvm::Function &F : M) {
    llvm::StringRef n = F.getName();
    if (!F.isDeclaration() &&
        (n.contains("wrapper") || n == "main" || n.starts_with("__SMACK") ||
         n.starts_with("__VERIFIER")) &&
        reachableFuncs.insert(&F).second)
      work.push_back(&F);
  }
  while (!work.empty()) {
    llvm::Function *F = work.back();
    work.pop_back();
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      auto *CB = dyn_cast<llvm::CallBase>(&*I);
      if (!CB)
        continue;
      if (auto *cf = CB->getCalledFunction()) {
        if (!cf->isDeclaration() && reachableFuncs.insert(cf).second)
          work.push_back(cf);
      } else if (!CB->isInlineAsm() && CB->getCalledOperand() &&
                 ms->hasValueNode(CB->getCalledOperand())) {
        if (auto *cn = ms->getCallICFGNode(CB))
          if (ander->hasIndCSCallees(cn))
            for (const SVF::FunObjVar *fo : ander->getIndCSCallees(cn)) {
              auto *cf = M.getFunction(fo->getName());
              if (cf && !cf->isDeclaration() && reachableFuncs.insert(cf).second)
                work.push_back(cf);
            }
      }
    }
  }
}

void DSAWrapper::buildUnionFind(llvm::Module &M) {
  // Union all objects that co-occur in any pointer's points-to set, over every
  // pointer-typed operand/result of every instruction (a sound superset of the
  // pointers SMACK will later query). Track memcpy/memset operand objects.
  auto unionPts = [&](const llvm::Value *p, bool memOpd) {
    if (!p || !ms->hasValueNode(p))
      return;
    const SVF::PointsTo &pts = ander->getPts(ms->getValueNode(p));
    unsigned first = 0;
    bool have = false;
    for (SVF::NodeID o : pts) {
      ufFind(o); // ensure present
      if (!have) {
        first = o;
        have = true;
      } else
        ufUnite(first, o);
      if (memOpd)
        memOpdObjs.insert(o);
    }
  };

  for (auto &F : M)
    for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
      Instruction *inst = &*I;
      bool isMemIntr = isa<MemCpyInst>(inst) || isa<MemSetInst>(inst) ||
                       isa<MemMoveInst>(inst);
      if (inst->getType()->isPointerTy())
        unionPts(inst, false);
      for (Use &U : inst->operands()) {
        Value *op = U.get();
        if (op && op->getType()->isPointerTy())
          unionPts(op, isMemIntr);
      }
    }

  // (R2) Field-vs-base severance fix: unite every GEP/field pointer with its
  // underlying base object's region. SVF's Andersen is field-SENSITIVE and can
  // resolve `ctx->field` to an object DISTINCT from the enclosing struct when
  // that field address is also handed interprocedurally. Observed in
  // aes_gcm_ct: `&ctx->y` (the GCM hash accumulator) passed to the indirect
  // GHASH resolves, inside br_gcm_run, to the callee-linked object (component
  // 2335), while br_gcm_get_tag reads the SAME field as an ordinary ctx
  // field-object (component 39, the ctx). So the accumulator the GHASH writes
  // is invisible to the tag finalization, and the GCM tag is computed over an
  // empty message (= the wrong-but-recognizable empty-message tag). A GEP
  // PROVABLY aliases its underlying object, so uniting their regions is sound
  // (merge-only) — the pointer-level analogue of the object-level field->base
  // collapse below, catching the pointers SVF did not base on the struct.
  auto uniteAll = [&](const SVF::PointsTo &pa, const SVF::PointsTo &pb) {
    if (pa.empty() || pb.empty())
      return;
    unsigned root = *pa.begin();
    ufFind(root);
    for (SVF::NodeID o : pa) { ufFind(o); ufUnite(root, o); }
    for (SVF::NodeID o : pb) { ufFind(o); ufUnite(root, o); }
  };
  auto uniteWithBase = [&](const llvm::Value *p) {
    if (!p || !p->getType()->isPointerTy() || !ms->hasValueNode(p))
      return;
    const llvm::Value *base = underlyingThroughSpill(p);
    if (!base || base == p || !ms->hasValueNode(base))
      return; // already a base, or untracked
    uniteAll(ander->getPts(ms->getValueNode(p)),
             ander->getPts(ms->getValueNode(base)));
  };
  for (auto &F : M)
    for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
      Instruction *inst = &*I;
      if (inst->getType()->isPointerTy())
        uniteWithBase(inst);
      for (Use &U : inst->operands())
        uniteWithBase(U.get());
    }

  // (R2-companion) Resolved indirect-call parameter binding. For the GHASH
  // dispatch `ctx->gh(&ctx->y, &ctx->h, ...)` the actual arg `&ctx->y` has
  // empty/no points-to in SVF (it could not resolve the interprocedural field
  // address), so the field<-base union above cannot relate it to the ctx; the
  // callee's non-empty formal param then sits in its own disjoint region. Since
  // an SVF-resolved indirect callee IS invoked with these args (devirt makes
  // the dispatch direct), unite each pointer formal's region with the actual
  // arg's UNDERLYING OBJECT (the ctx). The formal aliases a location inside that
  // object, so they must share a region. Sound (merge-only).
  for (auto &F : M)
    for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
      auto *CB = dyn_cast<llvm::CallBase>(&*I);
      if (!CB || CB->isInlineAsm() || CB->getCalledFunction())
        continue; // direct call / asm — Andersen already binds those
      const llvm::Value *fp = CB->getCalledOperand();
      if (!fp || !ms->hasValueNode(fp))
        continue;
      SVF::CallICFGNode *cnode = ms->getCallICFGNode(CB);
      if (!cnode || !ander->hasIndCSCallees(cnode))
        continue;
      for (const SVF::FunObjVar *fo : ander->getIndCSCallees(cnode)) {
        llvm::Function *callee = M.getFunction(fo->getName());
        if (!callee || callee->isDeclaration())
          continue;
        unsigned nn = CB->arg_size() < callee->arg_size() ? CB->arg_size()
                                                          : callee->arg_size();
        for (unsigned i = 0; i < nn; ++i) {
          const llvm::Value *arg = CB->getArgOperand(i);
          const llvm::Argument *formal = callee->getArg(i);
          if (!arg->getType()->isPointerTy() ||
              !formal->getType()->isPointerTy() || !ms->hasValueNode(formal))
            continue;
          const llvm::Value *abase = underlyingThroughSpill(arg);
          if (!abase || !ms->hasValueNode(abase))
            continue;
          uniteAll(ander->getPts(ms->getValueNode(formal)),
                   ander->getPts(ms->getValueNode(abase)));
        }
      }
    }

  // Realize true field-insensitivity: collapse every field/sub-object into its
  // base object. SVF's Andersen is field-SENSITIVE, so a buffer accessed at
  // distinct CONSTANT offsets yields distinct singleton GepObjVars that never
  // co-occur in any one points-to set — leaving each field in its own region.
  // The whole-buffer `__SMACK_values` annotation then binds to a single field
  // object that the per-byte stores miss, severing the buffer's data flow
  // (observed on aes_cbc_ct/ossl_aes_cbc; mee-cbc/aead escaped only because
  // their variable/loop offsets already collapse to the base in SVF). Uniting
  // each object with its base makes one buffer one region — coarser but sound,
  // and exactly the field-insensitivity getOffset()/isCollapsed() already claim.
  std::vector<unsigned> objs;
  objs.reserve(ufParent.size());
  for (auto &kv : ufParent)
    objs.push_back(kv.first);
  for (unsigned o : objs)
    if (pag->hasGNode(o))
      if (const SVF::BaseObjVar *bo = pag->getBaseObject(o))
        ufUnite(o, bo->getId());

  // SOUND CATCH-ALL. A LIVE mem-op pointer that SVF left unresolved (no region)
  // may alias ANY object; the split-memory invariant (may-alias => same region)
  // can then only be kept by putting everything in one region. Scan reachable
  // functions for such a pointer (the R1/R2/R3 resolvers above already handle the
  // ones SVF *can* resolve; dead code never executes so it cannot alias). If one
  // exists, collapse the whole partition into a single universal region. This is
  // the only sound treatment — there is no flag to turn it off.
  computeReachable(M);
  // Must check the SAME mem-op pointer set as the SMACK_AUDIT_REGION_SOUNDNESS
  // audit (load/store ptr + memcpy dest AND source), else the audit could flag a
  // live unresolved pointer the trigger missed.
  auto isLiveUnresolved = [&](const llvm::Value *addr) {
    if (!addr || rootPlus1(addr) != 0)
      return false;
    const llvm::Value *s = addr->stripPointerCasts();
    return !(isa<ConstantPointerNull>(s) || isa<UndefValue>(s) ||
             isRoConstData(addr));
  };
  bool liveUnresolved = false;
  for (auto &F : M) {
    if (!reachableFuncs.count(&F))
      continue;
    for (inst_iterator I = inst_begin(&F), E = inst_end(&F);
         I != E && !liveUnresolved; ++I) {
      if (auto *L = dyn_cast<LoadInst>(&*I))
        liveUnresolved = isLiveUnresolved(L->getPointerOperand());
      else if (auto *S = dyn_cast<StoreInst>(&*I))
        liveUnresolved = isLiveUnresolved(S->getPointerOperand());
      else if (auto *MI = dyn_cast<MemIntrinsic>(&*I)) {
        liveUnresolved = isLiveUnresolved(MI->getRawDest());
        if (!liveUnresolved)
          if (auto *MT = dyn_cast<MemTransferInst>(MI))
            liveUnresolved = isLiveUnresolved(MT->getRawSource());
      }
    }
    if (liveUnresolved)
      break;
  }
  if (liveUnresolved && !ufParent.empty()) {
    unsigned root = ufParent.begin()->first;
    ufFind(root);
    for (auto &kv : ufParent)
      ufUnite(root, kv.first);
    collapsed = true;
    collapsedRoot = ufFind(root);
    valueRootPlus1.clear(); // pre-collapse cached regions are now stale
    llvm::errs() << "[svf-region] SOUND CATCH-ALL engaged: a live unresolved "
                    "pointer forced a single universal region (sound, coarse)\n";
  }

  // Opt-in diagnostic: for vtable globals, dump each object's base + final
  // union-find component, to see why field-split globals (e.g. br_*_vtable)
  // land in different regions despite the field->base collapse above.
  if (std::getenv("SMACK_DEBUG_REGIONS")) {
    std::set<std::string> namedGlobals;
    for (unsigned o : objs) {
      if (!pag->hasGNode(o))
        continue;
      const SVF::BaseObjVar *bo = pag->getBaseObject(o);
      if (bo && ms->hasLLVMValue(bo))
        if (const llvm::Value *V = ms->getLLVMValue(bo))
          if (V->hasName() && llvm::isa<llvm::GlobalVariable>(V))
            namedGlobals.insert(V->getName().str());
    }
    llvm::errs() << "[REGIONDBG] union-find objs=" << objs.size()
                 << " named-global-objs=" << namedGlobals.size() << "\n";
    for (const auto &g : namedGlobals)
      llvm::errs() << "[REGIONDBG]   global-in-uf: " << g << "\n";
    // Also: is the vtable global even a tracked SVF value?
    for (llvm::GlobalVariable &G : module->globals())
      if (G.getName().contains("vtable"))
        llvm::errs() << "[REGIONDBG] module global '" << G.getName()
                     << "' hasValueNode=" << ms->hasValueNode(&G) << "\n";

    // Stage-0 mechanism probe: for every pointer load/store in the gcm/aes_ct/
    // static-init functions, log its union-find component (rootPlus1) and the
    // base-globals in the pointer's points-to. Lets us compare the static-init
    // store of the vtable fn-ptr (should carry the vtable) against the funcPtr
    // load through gc->bctx->vtable (which severs) — and see WHAT the load
    // resolves to instead of the vtable global.
    auto baseGlobalName = [&](SVF::NodeID o) -> std::string {
      if (!pag->hasGNode(o))
        return "";
      const SVF::BaseObjVar *bo = pag->getBaseObject(o);
      if (bo && ms->hasLLVMValue(bo))
        if (const llvm::Value *V = ms->getLLVMValue(bo))
          if (V->hasName())
            return V->getName().str();
      return "";
    };
    for (llvm::Function &F : M) {
      llvm::StringRef fn = F.getName();
      if (!(fn.contains("gcm") || fn.contains("aes_ct") ||
            fn.contains("static_init")))
        continue;
      for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
        const llvm::Value *addr = nullptr;
        const char *kind = nullptr;
        if (auto *L = dyn_cast<llvm::LoadInst>(&*I)) {
          if (!L->getType()->isPointerTy())
            continue; // only the fn-ptr / vtable-ptr chain
          addr = L->getPointerOperand();
          kind = "load.ptr";
        } else if (auto *S = dyn_cast<llvm::StoreInst>(&*I)) {
          if (!S->getValueOperand()->getType()->isPointerTy())
            continue;
          addr = S->getPointerOperand();
          kind = "store.ptr";
        }
        if (!addr || !ms->hasValueNode(addr))
          continue;
        const SVF::PointsTo &pts = ander->getPts(ms->getValueNode(addr));
        std::string bases;
        bool hasVtable = false;
        for (SVF::NodeID o : pts) {
          std::string g = baseGlobalName(o);
          if (!g.empty()) {
            bases += g + " ";
            if (g.find("vtable") != std::string::npos)
              hasVtable = true;
          }
        }
        llvm::errs() << "[REGIONDBG-OP] fn=" << fn.str() << " " << kind
                     << " comp=" << rootPlus1(addr)
                     << " ptsN=" << pts.count() << " vtable=" << hasVtable
                     << " bases={ " << bases << "}\n";
      }
    }

    // (R2) probe: for each SVF-resolved indirect callsite, log the funcPtr
    // load-address component vs the component(s) holding the resolved target
    // functions (reverse points-to). This pins down exactly which components
    // to union so the loaded fp matches the static-init store.
    if (std::getenv("SMACK_PROBE_DEVIRT")) {
      for (llvm::Function &F : M) {
        for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
          auto *CI = dyn_cast<llvm::CallInst>(&*I);
          if (!CI || CI->isInlineAsm() || CI->getCalledFunction())
            continue; // direct call / asm
          const llvm::Value *callee = CI->getCalledOperand();
          if (!ms->hasValueNode(callee))
            continue;
          SVF::CallICFGNode *cnode = ms->getCallICFGNode(CI);
          if (!cnode || !ander->hasIndCSCallees(cnode))
            continue;
          // funcPtr load address component (where the dispatch reads from).
          unsigned loadComp = 0;
          if (auto *L = dyn_cast<llvm::LoadInst>(callee->stripPointerCasts()))
            loadComp = rootPlus1(L->getPointerOperand());
          llvm::errs() << "[DEVIRT-PROBE] fn=" << F.getName().str()
                       << " calleePtsComp=" << rootPlus1(callee)
                       << " loadAddrComp=" << loadComp << "\n";
          for (const SVF::FunObjVar *fo : ander->getIndCSCallees(cnode)) {
            std::string holders;
            for (SVF::NodeID n : ander->getRevPts(fo->getId())) {
              std::string g = baseGlobalName(n);
              holders += "[" + (g.empty() ? std::string("?") : g) + " comp=" +
                         std::to_string(ufFind(n) + 1) + "] ";
            }
            llvm::errs() << "[DEVIRT-PROBE]   target=" << fo->getName()
                         << " heldBy=" << holders << "\n";
          }
        }
      }
    }
  }
}

void DSAWrapper::aggregateRegions() {
  // Collect a stable list of object ids first (ufFind mutates ufParent).
  std::vector<unsigned> objs;
  objs.reserve(ufParent.size());
  for (auto &kv : ufParent)
    objs.push_back(kv.first);

  for (unsigned obj : objs) {
    unsigned root = ufFind(obj);
    RegionInfo &ri = regionInfo[root];
    const SVF::BaseObjVar *bo = nullptr;
    // getBaseObject is valid for object nodes (FI and Gep); guard defensively.
    if (pag->hasGNode(obj))
      bo = pag->getBaseObject(obj);
    if (!bo) {
      ri.complicated = true;
      ri.incomplete = true;
      continue;
    }
    if (bo->isHeap() || bo->isStack())
      ri.allocated = true;
    if (bo->isBlackHoleObj()) {
      ri.complicated = true;
      ri.incomplete = true;
    }
    if (bo->isArray())
      ri.arrayLike = true;
    if (bo->isGlobalObj()) {
      ri.numGlobals++;
      if (ms->hasLLVMValue(bo))
        if (auto *GV = dyn_cast<GlobalVariable>(ms->getLLVMValue(bo)))
          if (GV->hasInitializer())
            ri.staticInitd = true;
    }
    if (memOpdObjs.count(obj))
      ri.memOpd = true;
  }
}

bool DSAWrapper::cachedSVF(SVF::LLVMModuleSet *&ms, SVF::SVFIR *&pag,
                           SVF::Andersen *&ander) {
  ms = g_svfModuleSet;
  pag = g_svfIR;
  ander = g_svfAndersen;
  return g_svfAndersen != nullptr;
}

bool DSAWrapper::runOnModule(llvm::Module &M) {
  module = &M;
  dataLayout = &M.getDataLayout();

  // Build SVF once (see g_svf* declarations above). Caveat: the legacy PM
  // re-runs DSAWrapper for the translation consumer after intervening transforms,
  // so accesses those passes create are not in the (first-built) SVF and resolve
  // to "no region" (rootPlus1==0), as do pointers SVF genuinely leaves with empty
  // points-to. Such accesses are currently isolated in a single shared region —
  // sound only insofar as SVF's empty-pts soundly means "points to nothing
  // tracked" (TODO: harden unresolved accesses to be conservative by
  // construction). Per-run maps below are rebuilt against the cached SVF (stable
  // node ids), so they stay consistent.
  if (g_svfAndersen == nullptr) {
    // NOTE: SVF mutates M in place (BreakConstantGEPs + UnifyFunctionExitNodes);
    // fine for llvm2bpl's one-shot use, and it preserves llvm::Value* identity for
    // the pointer queries below.
    SVF::LLVMModuleSet::buildSVFModule(M);
    g_svfModuleSet = SVF::LLVMModuleSet::getLLVMModuleSet();
    SVF::SVFIRBuilder builder;
    g_svfIR = builder.build();
    g_svfAndersen = SVF::AndersenWaveDiff::createAndersenWaveDiff(g_svfIR);
  }
  ms = g_svfModuleSet;
  pag = g_svfIR;
  ander = g_svfAndersen;

  buildUnionFind(M);
  aggregateRegions();

  // Soundness audit (opt-in): every load/store/mem-intrinsic pointer that gets
  // NO region (empty SVF points-to) is isolated from all real buffers — sound
  // ONLY if "empty pts" truly means "points to nothing" (null/undef). Classify
  // them so we can confirm none are real accesses SVF under-approximated (e.g.
  // unsummarized external-call results).
  if (std::getenv("SMACK_AUDIT_UNRESOLVED")) {
    std::map<std::string, unsigned> klass;
    std::map<std::string, std::string> example;
    unsigned total = 0;
    auto classify = [](const llvm::Value *p) -> std::string {
      const llvm::Value *s = p->stripPointerCasts();
      if (isa<ConstantPointerNull>(s))
        return "null";
      if (isa<UndefValue>(s))
        return "undef";
      if (auto *cb = dyn_cast<CallBase>(s))
        return cb->getCalledFunction()
                   ? (cb->getCalledFunction()->isDeclaration()
                          ? "extern-call-result"
                          : "call-result")
                   : "indirect-call-result";
      if (isa<LoadInst>(s))
        return "loaded-ptr";
      if (isa<Argument>(s))
        return "argument";
      if (isa<GetElementPtrInst>(s))
        return "gep";
      if (isa<Constant>(s))
        return "const";
      return "other";
    };
    // Walk casts/GEPs to an underlying read-only global (benign: constant data).
    auto readOnlyConstGlobal = [](const llvm::Value *p) {
      const llvm::Value *s = p->stripPointerCasts();
      while (true) {
        if (auto *g = dyn_cast<GlobalVariable>(s))
          return g->isConstant();
        if (auto *ce = dyn_cast<ConstantExpr>(s)) {
          if (ce->getOpcode() == Instruction::GetElementPtr) {
            s = ce->getOperand(0)->stripPointerCasts();
            continue;
          }
        }
        if (auto *gep = dyn_cast<GEPOperator>(s)) {
          s = gep->getPointerOperand()->stripPointerCasts();
          continue;
        }
        return false;
      }
    };
    unsigned riskyStores = 0, riskyLoads = 0;
    unsigned riskyNoNode = 0, riskyEmptyPts = 0;
    std::map<std::string, unsigned> riskyByFunc;
    std::string riskyExample;
    auto check = [&](const llvm::Value *p, bool isStore, const llvm::Function *F) {
      if (!p || !p->getType()->isPointerTy() || rootPlus1(p) != 0)
        return;
      std::string k = classify(p);
      if (!klass.count(k)) {
        std::string s;
        llvm::raw_string_ostream os(s);
        p->print(os);
        example[k] = s;
      }
      klass[k]++;
      total++;
      // RISKY = a no-region access that could alias a real buffer: not null/undef,
      // and not a read-only constant global (those are benign constant data).
      if (k == "null" || k == "undef" || readOnlyConstGlobal(p))
        return;
      (isStore ? riskyStores : riskyLoads)++;
      (ms->hasValueNode(p) ? riskyEmptyPts : riskyNoNode)++;
      riskyByFunc[F->getName().str()]++;
      if (isStore && riskyExample.empty()) {
        llvm::raw_string_ostream os(riskyExample);
        p->print(os);
      }
    };
    for (auto &F : M)
      for (auto &BB : F)
        for (auto &I : BB) {
          if (auto *L = dyn_cast<LoadInst>(&I))
            check(L->getPointerOperand(), false, &F);
          else if (auto *S = dyn_cast<StoreInst>(&I))
            check(S->getPointerOperand(), true, &F);
          else if (auto *MI = dyn_cast<MemIntrinsic>(&I)) {
            check(MI->getRawDest(), true, &F);
            if (auto *MT = dyn_cast<MemTransferInst>(MI))
              check(MT->getRawSource(), false, &F);
          }
        }
    llvm::errs() << "[svf-audit] mem-access pointers with NO region (empty pts): "
                 << total << "\n";
    for (auto &kv : klass)
      llvm::errs() << "[svf-audit]   " << kv.first << ": " << kv.second
                   << "   e.g. " << example[kv.first] << "\n";
    llvm::errs() << "[svf-audit] RISKY (no region, not null/undef, not read-only-const): "
                 << "stores=" << riskyStores << " loads=" << riskyLoads
                 << "  [no-SVF-node=" << riskyNoNode
                 << " has-node-but-empty-pts=" << riskyEmptyPts << "]\n";
    for (auto &kv : riskyByFunc)
      llvm::errs() << "[svf-audit]   in fn " << kv.first << ": " << kv.second << "\n";
    if (!riskyExample.empty())
      llvm::errs() << "[svf-audit]   risky store e.g. " << riskyExample << "\n";
  }

  // Comprehensive region-soundness self-audit. The split-memory model is sound
  // iff may-alias => same region. This checks the three ways that invariant can
  // break in the region DERIVATION (it cannot check SVF's own points-to
  // completeness — only an end-to-end byte-match can):
  //   C1 multi-component pointer: a mem-op pointer whose points-to spans >1
  //      union-find component — it aliases objects in 2 regions but is assigned
  //      one (the union-find failed to unite co-occurring objects).
  //   C2 unresolved mem-op: a load/store/memcpy pointer with NO region (post-R1)
  //      that is not null/undef/read-only-const — it lands in the catch-all and
  //      is NOT merged with any RESOLVED region it may alias.
  //   C3 cross-region object: one SVF object reached by mem-op pointers assigned
  //      to >1 region — the same memory split across regions.
  // verdict=SOUND iff all three are zero (modulo SVF points-to completeness).
  if (std::getenv("SMACK_AUDIT_REGION_SOUNDNESS")) {
    auto roConst = [](const llvm::Value *p) {
      const llvm::Value *s = p->stripPointerCasts();
      while (true) {
        if (auto *g = dyn_cast<GlobalVariable>(s))
          return g->isConstant();
        if (auto *ce = dyn_cast<ConstantExpr>(s))
          if (ce->getOpcode() == Instruction::GetElementPtr) {
            s = ce->getOperand(0)->stripPointerCasts();
            continue;
          }
        if (auto *gep = dyn_cast<GEPOperator>(s)) {
          s = gep->getPointerOperand()->stripPointerCasts();
          continue;
        }
        return false;
      }
    };
    // Reachable (LIVE) functions: BFS the call graph (direct + SVF-resolved
    // indirect edges) from the entry roots. C2 in UNREACHABLE (dead) functions
    // — e.g. BearSSL AEAD-vtable functions the harness never calls — is benign:
    // dead code never executes, so its mem-ops cannot cause a real severance.
    std::unordered_set<const llvm::Function *> reachable;
    {
      std::vector<llvm::Function *> work;
      for (llvm::Function &F : M) {
        llvm::StringRef n = F.getName();
        if (!F.isDeclaration() &&
            (n.contains("wrapper") || n == "main" || n.starts_with("__SMACK") ||
             n.starts_with("__VERIFIER")) &&
            reachable.insert(&F).second)
          work.push_back(&F);
      }
      while (!work.empty()) {
        llvm::Function *F = work.back();
        work.pop_back();
        for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
          auto *CB = dyn_cast<llvm::CallBase>(&*I);
          if (!CB)
            continue;
          if (auto *cf = CB->getCalledFunction()) {
            if (!cf->isDeclaration() && reachable.insert(cf).second)
              work.push_back(cf);
          } else if (!CB->isInlineAsm() &&
                     ms->hasValueNode(CB->getCalledOperand())) {
            if (auto *cn = ms->getCallICFGNode(CB))
              if (ander->hasIndCSCallees(cn))
                for (const SVF::FunObjVar *fo : ander->getIndCSCallees(cn)) {
                  auto *cf = M.getFunction(fo->getName());
                  if (cf && !cf->isDeclaration() && reachable.insert(cf).second)
                    work.push_back(cf);
                }
          }
        }
      }
    }
    std::unordered_map<unsigned, unsigned> objRegion; // SVF obj -> region
    std::unordered_set<unsigned> crossObjs;
    unsigned multiComp = 0, memOps = 0, liveC2 = 0, deadC2 = 0;
    std::string riskyEg;
    std::map<std::string, unsigned> c2ByFunc;
    auto audit = [&](const llvm::Value *p, const llvm::Function *F) {
      if (!p || !p->getType()->isPointerTy())
        return;
      ++memOps;
      unsigned r = rootPlus1(p);
      if (r == 0) { // C2: no region
        const llvm::Value *s = p->stripPointerCasts();
        if (isa<ConstantPointerNull>(s) || isa<UndefValue>(s) || roConst(p))
          return; // benign
        if (!reachable.count(F)) {
          ++deadC2; // dead code — never executes, benign
          return;
        }
        ++liveC2;
        ++c2ByFunc[F->getName().str()];
        if (riskyEg.empty()) {
          llvm::raw_string_ostream os(riskyEg);
          p->print(os);
        }
        return;
      }
      if (!ms->hasValueNode(p))
        return;
      const SVF::PointsTo &pts = ander->getPts(ms->getValueNode(p));
      if (pts.empty())
        return;
      unsigned c0 = ufFind(*pts.begin());
      bool multi = false;
      for (SVF::NodeID o : pts) {
        if (ufFind(o) != c0)
          multi = true; // C1
        auto it = objRegion.find(o);
        if (it == objRegion.end())
          objRegion[o] = r;
        else if (it->second != r)
          crossObjs.insert(o); // C3
      }
      if (multi)
        ++multiComp;
    };
    for (auto &F : M)
      for (auto &BB : F)
        for (auto &I : BB) {
          if (auto *L = dyn_cast<LoadInst>(&I))
            audit(L->getPointerOperand(), &F);
          else if (auto *S = dyn_cast<StoreInst>(&I))
            audit(S->getPointerOperand(), &F);
          else if (auto *MI = dyn_cast<MemIntrinsic>(&I)) {
            audit(MI->getRawDest(), &F);
            if (auto *MT = dyn_cast<MemTransferInst>(MI))
              audit(MT->getRawSource(), &F);
          }
        }
    // verdict=SOUND iff the derivation is faithful (C1/C3=0) and no LIVE
    // (reachable) mem-op is unresolved. Dead-code C2 is reported but does not
    // affect the verdict — it never executes.
    bool sound = multiComp == 0 && liveC2 == 0 && crossObjs.empty();
    llvm::errs() << "[REGION-SOUNDNESS] memOps=" << memOps
                 << " C1_multiComp=" << multiComp << " C2_liveUnresolved="
                 << liveC2 << " C2_deadUnresolved=" << deadC2
                 << " C3_crossRegionObj=" << crossObjs.size()
                 << " verdict=" << (sound ? "SOUND" : "SUSPECT") << "\n";
    if (!riskyEg.empty())
      llvm::errs() << "[REGION-SOUNDNESS]   live-C2 e.g. " << riskyEg << "\n";
    if (std::getenv("SMACK_AUDIT_C2_DETAIL"))
      for (auto &kv : c2ByFunc)
        llvm::errs() << "[REGION-SOUNDNESS]   live-C2-in-fn " << kv.first << ": "
                     << kv.second << "\n";
  }

  return false; // NOTE: SVF did mutate M, but we report "unchanged" to the PM;
                // downstream SMACK passes consume the (semantically-equivalent)
                // mutated module.
}

DSAWrapper::~DSAWrapper() {
  // One-shot tool: let process exit reclaim SVF singletons. Releasing here is
  // unsafe because SmackRep/translation may still hold llvm::Value*s into the
  // SVF-touched module.
}

unsigned DSAWrapper::rootPlus1(const llvm::Value *v) {
  auto it = valueRootPlus1.find(v);
  if (it != valueRootPlus1.end())
    return it->second;
  unsigned result = 0;
  if (v && ms && ms->hasValueNode(v)) {
    const SVF::PointsTo &pts = ander->getPts(ms->getValueNode(v));
    if (pts.count() > 0)
      result = ufFind(*pts.begin()) + 1;
  }
  // (R1) Base-object region fallback. A GEP/field pointer that SVF gave no
  // value-node OR an empty points-to (e.g. the GEP'd vtable-field stores SMACK
  // emits in __SMACK_static_init, or `ctx->y` field addresses whose
  // interprocedural points-to SVF could not resolve) would otherwise get region
  // 0 and collapse into the catch-all (incomplete) region, severed from the
  // object it actually lives in. A GEP result PROVABLY aliases its underlying
  // object, so inheriting that object's region is sound (it only adds a
  // may-alias, never removes one). Restricted to identifiable base objects
  // (global / argument / alloca) — the objects SVF models precisely — so this
  // won't conflate unrelated pointers.
  if (result == 0 && v && ms) {
    const llvm::Value *base = underlyingThroughSpill(v);
    if (base && base != v && ms->hasValueNode(base) &&
        (llvm::isa<llvm::GlobalVariable>(base) ||
         llvm::isa<llvm::Argument>(base) || llvm::isa<llvm::AllocaInst>(base))) {
      const SVF::PointsTo &bpts = ander->getPts(ms->getValueNode(base));
      if (bpts.count() > 0)
        result = ufFind(*bpts.begin()) + 1;
    }
  }
  // SOUND catch-all: once collapsed, a still-unresolved (non-benign) pointer
  // maps to the single universal region — it may alias anything, and everything
  // resolved was already united into that region. (Resolved pointers reach here
  // with result != 0 already == collapsedRoot+1, since unite-all merged their
  // objects; only genuinely unresolved ones need this override.)
  if (collapsed && result == 0 && v) {
    const llvm::Value *s = v->stripPointerCasts();
    if (!isa<ConstantPointerNull>(s) && !isa<UndefValue>(s) && !isRoConstData(v))
      result = collapsedRoot + 1;
  }
  valueRootPlus1[v] = result;
  return result;
}

const DSAWrapper::RegionInfo *DSAWrapper::infoOf(MemNodeRef n) {
  if (!n)
    return nullptr;
  unsigned root = decode(n) - 1;
  auto it = regionInfo.find(root);
  return it == regionInfo.end() ? nullptr : &it->second;
}

MemNodeRef DSAWrapper::getNode(const llvm::Value *v) {
  unsigned r = rootPlus1(v);
  return r ? encode(r) : nullptr;
}

unsigned DSAWrapper::getOffset(const llvm::Value *) {
  // Field-insensitive partition (spike): each region is one collapsed component.
  return 0;
}

unsigned DSAWrapper::getPointedTypeSize(const llvm::Value *v) {
  // Opaque-pointer-safe: recover the access width from v's load/store users.
  for (const User *u : v->users()) {
    if (auto *L = dyn_cast<LoadInst>(u))
      if (L->getPointerOperand() == v)
        return dataLayout->getTypeStoreSize(L->getType());
    if (auto *S = dyn_cast<StoreInst>(u))
      if (S->getPointerOperand() == v)
        return dataLayout->getTypeStoreSize(S->getValueOperand()->getType());
  }
  return 1;
}

bool DSAWrapper::isRead(const llvm::Value *) {
  // Conservative: assume read (CodifyStaticInits then codifies initializers —
  // sound to over-approximate).
  return true;
}

bool DSAWrapper::isTypeSafe(const llvm::Value *) {
  // Conservative (spike): never treat a region as type-safe, which disables the
  // singleton optimization. Sound; loses some precision/perf to be revisited.
  return false;
}

unsigned DSAWrapper::getNumGlobals(MemNodeRef n) {
  auto *i = infoOf(n);
  return i ? i->numGlobals : 0;
}
bool DSAWrapper::isStaticInitd(MemNodeRef n) {
  auto *i = infoOf(n);
  return i && i->staticInitd;
}
bool DSAWrapper::isMemOpd(MemNodeRef n) {
  auto *i = infoOf(n);
  return i && i->memOpd;
}
bool DSAWrapper::isAllocated(MemNodeRef n) {
  auto *i = infoOf(n);
  return !i || i->allocated; // unknown -> conservative (allocated)
}
bool DSAWrapper::isComplicated(MemNodeRef n) {
  auto *i = infoOf(n);
  return !i || i->complicated;
}
bool DSAWrapper::isIncomplete(MemNodeRef n) {
  auto *i = infoOf(n);
  return !i || i->incomplete;
}
bool DSAWrapper::isArray(MemNodeRef n) {
  auto *i = infoOf(n);
  return i && i->arrayLike;
}
bool DSAWrapper::isCollapsed(MemNodeRef) {
  // Field-insensitive partition (spike).
  return true;
}

} // namespace smack

char smack::DSAWrapper::ID = 0;

using namespace smack;
INITIALIZE_PASS(DSAWrapper, "smack-dsa-wrapper",
                "SMACK SVF-based Memory Region Partition Wrapper", false, false)
