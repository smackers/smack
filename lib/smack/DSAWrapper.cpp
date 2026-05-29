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

#include "MemoryModel/PointsTo.h"
#include "SVF-LLVM/LLVMModule.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "SVFIR/SVFVariables.h"
#include "Util/SVFUtil.h"
#include "WPA/Andersen.h"

#define DEBUG_TYPE "smack-dsa-wrapper"

namespace smack {

using namespace llvm;

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

bool DSAWrapper::runOnModule(llvm::Module &M) {
  module = &M;
  dataLayout = &M.getDataLayout();

  // SVF is built ONCE into process-global statics and reused across DSAWrapper
  // re-runs: SVF cannot be rebuilt in-process (release()+rebuild trips
  // SVFIRBuilder::initialiseNodes' node/sym-count assert — its many singletons do
  // not fully reset). Caveat: the legacy PM re-runs DSAWrapper for the translation
  // consumer after intervening transforms, so accesses those passes create are not
  // in the (first-built) SVF and resolve to "no region" (rootPlus1==0), as do
  // pointers SVF genuinely leaves with empty points-to. Such accesses are currently
  // isolated in a single shared region — sound only insofar as SVF's empty-pts
  // soundly means "points to nothing tracked" (TODO: harden unresolved accesses to
  // be conservative by construction). Per-run maps below are rebuilt against the
  // cached SVF (stable node ids), so they stay consistent.
  static SVF::LLVMModuleSet *s_ms = nullptr;
  static SVF::SVFIR *s_pag = nullptr;
  static SVF::Andersen *s_ander = nullptr;
  if (s_ander == nullptr) {
    // NOTE: SVF mutates M in place (BreakConstantGEPs + UnifyFunctionExitNodes);
    // fine for llvm2bpl's one-shot use, and it preserves llvm::Value* identity for
    // the pointer queries below.
    SVF::LLVMModuleSet::buildSVFModule(M);
    s_ms = SVF::LLVMModuleSet::getLLVMModuleSet();
    SVF::SVFIRBuilder builder;
    s_pag = builder.build();
    s_ander = SVF::AndersenWaveDiff::createAndersenWaveDiff(s_pag);
  }
  ms = s_ms;
  pag = s_pag;
  ander = s_ander;

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
