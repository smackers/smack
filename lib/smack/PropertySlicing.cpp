//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/PropertySlicing.h"
#include "smack/DSAWrapper.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/Regions.h"
#include "smack/SmackOptions.h"

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <cctype>

#include <chrono>
#include <limits>
#include <map>
#include <queue>

#define DEBUG_TYPE "property-slicing"

namespace smack {

using namespace llvm;

// ---------------------------------------------------------------- options

const llvm::cl::opt<bool> PropertySlicingEnabled(
    "property-slicing",
    llvm::cl::desc("Remove program behaviour that cannot influence the "
                   "assertion property before Boogie generation."));

const llvm::cl::opt<bool> PropertySlicingNoLoopBypass(
    "property-slicing-no-loop-bypass",
    llvm::cl::desc("Property slicing: remove irrelevant instructions but keep "
                   "every loop (for isolating correctness failures)."));

const llvm::cl::opt<bool> PropertySlicingRelaxAsm(
    "property-slicing-relax-asm",
    llvm::cl::desc("Property slicing: treat inline asm as the no-op SMACK's "
                   "own translation already makes it."));

const llvm::cl::opt<bool> PropertySlicingNoRegions(
    "property-slicing-no-regions",
    llvm::cl::desc("Property slicing: ignore the region partition and treat "
                   "all memory as one object (ablation experiment)."));

/// SMACK's concurrency mode -- share/smack/top.py passes this alongside
/// -property-slicing whenever the user gave --pthread. It describes the
/// *program* rather than this pass, so it belongs in SmackOptions next to
/// -memory-safety and -integer-overflow; it is declared here only because the
/// slicer is its single consumer (the refusal in propertySlicingWillRun()).
const llvm::cl::opt<bool> PropertySlicingPthread(
    "property-slicing-pthread",
    llvm::cl::desc("Property slicing: the translated program is concurrent "
                   "(SMACK's --pthread); slicing is refused for it."));

const llvm::cl::opt<std::string> PropertySlicingProfile(
    "property-slicing-profile",
    llvm::cl::desc("Write a machine-readable property-slicing profile here."),
    llvm::cl::value_desc("filename"));

namespace {

/// A helper that never lies about not knowing: any callee we cannot resolve to
/// a single Function is treated as unknown.
const Function *calleeOf(const CallInst &CI) {
  if (auto F = CI.getCalledFunction())
    return F;
  if (auto V = CI.getCalledOperand())
    if (auto F = dyn_cast<Function>(V->stripPointerCastsAndAliases()))
      return F;
  return nullptr;
}

/// Control dependence, computed from the post-dominator tree by the standard
/// edge-walk: for every CFG edge A->S where S does not post-dominate A, every
/// node on the post-dominator path from S up to (but excluding) ipdom(A) is
/// control-dependent on A. Linear in the size of the post-dominator tree paths
/// walked, so it stays within the "cheap analyses only" budget.
/// Blocks from which a function exit is reachable. Post-dominance is only
/// meaningful for these: LLVM's PostDominatorTree still yields a tree over a
/// reverse-unreachable region (an infinite loop), but the immediate
/// post-dominator it picks there is an artifact of how the virtual root is
/// attached, not a semantic one. Measured on test/c/basic/jain_5_true.c --
/// `while (1) { ...; assert(x != 30); }`, a function with no return at all --
/// the tree named the *taken* successor as ipdom of the deciding block, so the
/// assertion's own guard came out control-dependent on nothing, was replaced
/// by undef, and turned a verified program into a spurious error.
void collectExitReaching(Function &F,
                         std::unordered_set<const BasicBlock *> &R) {
  std::vector<const BasicBlock *> work;
  for (auto &BB : F) {
    auto *T = BB.getTerminator();
    if (isa<ReturnInst>(T) || isa<UnreachableInst>(T) || isa<ResumeInst>(T)) {
      R.insert(&BB);
      work.push_back(&BB);
    }
  }
  while (!work.empty()) {
    auto *B = work.back();
    work.pop_back();
    for (auto *P : predecessors(B))
      if (R.insert(P).second)
        work.push_back(P);
  }
}

void computeControlDependence(
    Function &F, PostDominatorTree &PDT,
    const std::unordered_set<const BasicBlock *> &ExitReaching,
    std::unordered_map<const BasicBlock *, std::vector<const BasicBlock *>>
        &CD) {
  for (auto &A : F) {
    auto *T = A.getTerminator();
    if (!T || T->getNumSuccessors() < 2)
      continue;
    if (!ExitReaching.count(&A))
      continue; // post-dominance undefined here; the branch is kept instead
    auto *ANode = PDT.getNode(&A);
    if (!ANode)
      continue;
    auto *AIdom = ANode->getIDom();
    for (auto *S : successors(&A)) {
      auto *N = PDT.getNode(S);
      while (N && N != AIdom) {
        if (N->getBlock())
          CD[N->getBlock()].push_back(&A);
        N = N->getIDom();
      }
    }
  }
}

double secondsSince(std::chrono::steady_clock::time_point T0) {
  return std::chrono::duration<double>(std::chrono::steady_clock::now() - T0)
      .count();
}

} // namespace

const char *PropertySlicing::reasonName(LoopReason R) {
  switch (R) {
  case LoopReason::ERROR_REACHABLE:
    return "ERROR_REACHABLE";
  case LoopReason::RELEVANT_SCALAR:
    return "RELEVANT_SCALAR";
  case LoopReason::RELEVANT_REGION:
    return "RELEVANT_REGION";
  case LoopReason::CONTROL:
    return "CONTROL";
  case LoopReason::UNKNOWN_CALL:
    return "UNKNOWN_CALL";
  case LoopReason::VOLATILE_ATOMIC:
    return "VOLATILE_ATOMIC";
  case LoopReason::DSA_COLLAPSED_REGION:
    return "DSA_COLLAPSED_REGION";
  case LoopReason::ESCAPING_VALUE:
    return "ESCAPING_VALUE";
  case LoopReason::NO_PREHEADER:
    return "NO_PREHEADER";
  case LoopReason::MULTIPLE_EXITS:
    return "MULTIPLE_EXITS";
  case LoopReason::NO_EXIT:
    return "NO_EXIT";
  case LoopReason::OTHER_CONSERVATIVE:
    return "OTHER_CONSERVATIVE";
  case LoopReason::BYPASSED:
    return "BYPASSED";
  }
  return "OTHER_CONSERVATIVE";
}

void PropertySlicing::getAnalysisUsage(AnalysisUsage &AU) const {
  // The pass only deletes instructions and blocks; it never creates a memory
  // operation. The region partition computed on the pre-slice module is
  // therefore coarser than or equal to one computed afterwards, which is the
  // conservative direction for a memory model -- so Regions (and the sea-DSA
  // graph its Nodes point into) stay valid and are explicitly preserved,
  // sparing a second whole-module DSA run. LoopInfo/PostDominatorTree are
  // deliberately NOT preserved: the CFG does change.
  AU.addRequired<Regions>();
  AU.addRequired<DSAWrapper>();
  AU.addPreserved<Regions>();
  AU.addPreserved<DSAWrapper>();
  AU.addRequired<PostDominatorTreeWrapperPass>();
  AU.addRequired<LoopInfoWrapperPass>();
}

// ------------------------------------------------------------- predicates

/// The property root. SMACK does not mark it in the IR at all: for SV-COMP,
/// `call reach_error()` is rewritten to `assert false; call reach_error();` by
/// a textual pass over the generated .bpl (share/smack/top.py, in
/// replace_reach_error), long after this pass has run. The root at this point
/// in the pipeline is therefore purely a call to a specially-named function,
/// and the set below is exactly the set of names that later become Boogie
/// asserts or otherwise carry verification semantics.
bool PropertySlicing::isPropertyRoot(const CallInst &CI) const {
  auto F = calleeOf(CI);
  if (!F || !F->hasName())
    return false;
  auto N = F->getName();
  // SV-COMP unreach-call: rewritten to `assert false` after translation.
  if (N == "reach_error")
    return true;
  // SMACK's own assertion, and the Rust panic marker.
  if (N == "__VERIFIER_assert" || N == Naming::RUST_PANIC_MARKER)
    return true;
  return false;
}

/// Calls that change the verification state or emit Boogie text, and so must
/// never be elided. Every name here is taken from SMACK's own dispatch --
/// SmackInstGenerator::visitCallInst (lib/smack/SmackInstGenerator.cpp:638-700)
/// and the Naming constants (lib/smack/Naming.cpp:25-60) -- rather than from
/// intuition about what a `__VERIFIER_`-looking name might mean.
///
/// The distinction that matters most for the slice is that a *nondeterminism*
/// function is pure: `__VERIFIER_nondet_*` and `__SMACK_nondet_*` merely yield
/// an unconstrained value, and SMACK itself treats them as ordinary external
/// calls whose only content is that value (note EXTERNAL_PROC_IGNORE at
/// SmackInstGenerator.cpp:39 exempting `__VERIFIER_nondet` from even the
/// external-address assumption). Classifying them as verification effects made
/// every function that draws a nondeterministic value un-droppable, and by
/// transitivity poisoned nearly the whole call graph.
bool PropertySlicing::hasVerificationEffect(const CallInst &CI) const {
  auto F = calleeOf(CI);
  if (!F || !F->hasName())
    return false;
  auto N = F->getName();

  // Pure value producers and the arithmetic models: droppable when the result
  // is irrelevant. __SMACK_and*/__SMACK_or* come from RewriteBitwiseOps
  // (RewriteBitwiseOps.cpp:107-142); this pass runs before it, but the guard
  // keeps the predicate correct if that order changes.
  if (N.contains("__VERIFIER_nondet") || N.contains("__SMACK_nondet") ||
      N.startswith("__SMACK_and") || N.startswith("__SMACK_or") ||
      N == "__SMACK_dummy")
    return false;

  // Assertions and assumptions constrain or check the state.
  if (N == "__VERIFIER_assert" || N == "__VERIFIER_assume" ||
      N == "reach_error" || N == Naming::RUST_PANIC_MARKER)
    return true;

  // Annotations that become Boogie text verbatim. SMACK matches these as
  // substrings, so match them the same way.
  for (auto &P :
       {Naming::CODE_PROC, Naming::DECL_PROC, Naming::TOP_DECL_PROC,
        Naming::MOD_PROC, Naming::VALUE_PROC, Naming::RETURN_VALUE_PROC,
        Naming::DECLARATIONS_PROC, Naming::STATIC_INIT_PROC, Naming::LOOP_EXIT,
        Naming::CONTRACT_REQUIRES, Naming::CONTRACT_ENSURES,
        Naming::CONTRACT_INVARIANT, Naming::CONTRACT_FORALL,
        Naming::CONTRACT_EXISTS})
    if (N.contains(P))
      return true;

  return false;
}

/// Effects the region abstraction does not capture. Retained unconditionally.
///
/// Note what is NOT here. A *volatile* load or store is an ordinary load or
/// store to SMACK: nothing in the translator inspects LoadInst/StoreInst
/// volatility (the only isVolatile() reads in the tree are SmackRep.cpp:322 and
/// :346, which pass the flag through to the memcpy/memset models), and Regions
/// registers those pointers like any other. Treating volatility as an
/// unmodelled effect here would make the slicer stricter than the semantics it
/// is slicing, for no soundness gain.
bool PropertySlicing::hasUnmodelledEffect(const Instruction &I) const {
  // Atomicity is not here either, and for the same reason. SMACK translates
  // AtomicCmpXchg and AtomicRMW as a plain load followed by a plain store on
  // the same region (SmackInstGenerator.cpp:551-576) -- the ordering and the
  // atomicity are simply dropped -- and visitLoadInst/visitStoreInst never
  // consult an ordering at all. Regions registers all four instruction kinds
  // (Regions.cpp, visitAtomicCmpXchgInst/visitAtomicRMWInst), so the region
  // rules already cover them exactly as they cover ordinary memory. Treating
  // them as unmodelled cost 12 of the 77 un-droppable seeds on the he.ko
  // driver task for no soundness gain.
  if (isa<FenceInst>(&I))
    return true;
  if (auto CI = dyn_cast<CallInst>(&I)) {
    if (CI->isInlineAsm())
      // SmackInstGenerator.cpp:641-646 already translates every inline asm to
      // Stmt::skip() -- a complete no-op -- and warns that this "can lead to
      // both false alarms and missed detections". Under -property-slicing-
      // relax-asm the slicer adopts that same semantics, which cannot lose an
      // error the translator would have kept. It is off by default so the
      // prototype's baseline retains anything the region abstraction does not
      // capture.
      return !PropertySlicingRelaxAsm;
    if (!calleeOf(*CI))
      return true; // unresolved indirect target
  }
  if (isa<InvokeInst>(&I) || isa<ResumeInst>(&I) || isa<LandingPadInst>(&I))
    return true;
  if (isa<IndirectBrInst>(&I) || isa<CallBrInst>(&I))
    return true;
  return false;
}

// ------------------------------------------------------------- call graph

void PropertySlicing::computeMayReachError(Module &M) {
  std::unordered_map<const Function *, std::vector<const Function *>> callers;
  std::queue<const Function *> work;

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    bool root = false;
    for (auto &I : instructions(F)) {
      if (auto CI = dyn_cast<CallInst>(&I)) {
        if (isPropertyRoot(*CI))
          root = true;
        if (auto G = calleeOf(*CI))
          callers[G].push_back(&F);
        else if (!CI->isInlineAsm())
          // An unresolved indirect call may reach anything. Inline asm cannot
          // reach a C function at all, and counting it here marked 33 extra
          // functions on he.ko as error-reaching.
          root = true;
      }
    }
    if (root && !mayReachError.count(&F)) {
      mayReachError.insert(&F);
      work.push(&F);
    }
  }

  while (!work.empty()) {
    auto F = work.front();
    work.pop();
    for (auto C : callers[F])
      if (!mayReachError.count(C)) {
        mayReachError.insert(C);
        work.push(C);
      }
  }
}

/// `unsafeToDrop` and `writtenRegions` in one greatest-fixpoint pass.
/// Optimistic initialisation (everything droppable) is what makes recursive
/// but effect-free functions droppable; the iteration only ever removes
/// safety, so it converges.
void PropertySlicing::computeEffects(Module &M) {
  std::unordered_map<const Function *, std::vector<const Function *>> callees;

  for (auto &F : M) {
    if (F.isDeclaration()) {
      // No body: unknown effects unless LLVM itself proves otherwise.
      if (!F.doesNotAccessMemory() && !F.onlyReadsMemory())
        unsafeToDrop.insert(&F);
      continue;
    }
    auto &W = writtenRegions[&F];
    for (auto &I : instructions(F)) {
      if (hasUnmodelledEffect(I)) {
        if (unsafeToDrop.insert(&F).second)
          unsafeWhy[&F] =
              isa<CallInst>(&I) && cast<CallInst>(&I)->isInlineAsm()
                  ? "inline_asm"
                  : (isa<CallInst>(&I) ? "indirect_call" : "atomic");
      }
      if (isa<StoreInst>(&I) || isa<MemIntrinsic>(&I) ||
          isa<AtomicRMWInst>(&I) || isa<AtomicCmpXchgInst>(&I)) {
        unsigned r = destRegion(I);
        if (r == TOP_REGION)
          writesTop.insert(&F);
        else
          W.insert(r);
      }

      if (auto CI = dyn_cast<CallInst>(&I)) {
        if (hasVerificationEffect(*CI)) {
          if (unsafeToDrop.insert(&F).second)
            unsafeWhy[&F] = "verification_effect";
        }
        if (auto G = calleeOf(*CI))
          callees[&F].push_back(G);
      }
    }
    if (mayReachError.count(&F))
      if (unsafeToDrop.insert(&F).second)
        unsafeWhy[&F] = "may_reach_error";
  }

  bool changed = true;
  while (changed) {
    changed = false;
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      auto &W = writtenRegions[&F];
      for (auto G : callees[&F]) {
        if (unsafeToDrop.count(G) && !unsafeToDrop.count(&F)) {
          unsafeToDrop.insert(&F);
          unsafeWhy[&F] = "callee:" + G->getName().str();
          changed = true;
        }
        if (writesTop.count(G) && !writesTop.count(&F)) {
          writesTop.insert(&F);
          changed = true;
        }
        auto it = writtenRegions.find(G);
        if (it == writtenRegions.end())
          continue;
        for (auto r : it->second)
          if (W.insert(r).second)
            changed = true;
      }
    }
  }
}

// ------------------------------------------------------------- relevance

/// A pointer whose object SMACK's region machinery cannot pin down.
///
/// This is the hole that matters most for a slicer. When `DSAWrapper::getNode`
/// returns null, `Region::init` sets incomplete = complicated = collapsed =
/// true, but `Region::overlaps` only unifies two *complicated* regions -- and
/// `Node::isIncomplete()` is dead in the pinned sea-DSA (it has no setter), so
/// the `incomplete && R.incomplete` disjunct never fires against a real node.
/// A cell-less pointer therefore receives its OWN region, disjoint from every
/// ordinary one, and `idx(p) != idx(q)` comes back for pointers that may very
/// well alias. sea-DSA's own `mayAlias` returns true in exactly this case.
/// SMACK's memory model lives with that; a slicer that used it to *delete* a
/// store would not be sound, so such accesses are forced to TOP_REGION here.
bool PropertySlicing::isOpaquePointer(const Value *Ptr) const {
  if (!Ptr || isa<ConstantPointerNull>(Ptr) || isa<UndefValue>(Ptr))
    return true;
  if (!DSA)
    return true;
  return DSA->getNode(Ptr) == nullptr;
}

namespace {
/// Length a memory intrinsic accesses, or UINT_MAX when it is not constant --
/// which Regions also uses, and which makes `Region::isDisjoint`'s unsigned
/// `offset + length` wrap at any non-zero offset and report a false
/// disjointness (Regions.cpp:68-71, plain `unsigned`, unlike `merge` at :75).
unsigned intrinsicLength(const MemIntrinsic &MI) {
  if (auto CI = dyn_cast<ConstantInt>(MI.getLength()))
    return CI->getZExtValue();
  return std::numeric_limits<unsigned>::max();
}
} // namespace

/// Freeze the region partition before any slicing decision depends on it.
///
/// `Regions::idx` is stateful: it constructs a fresh Region on every call,
/// merges it into the first overlapping entry, then cascades -- and the
/// cascade calls `regions.erase`, which renumbers every index above it. Indices
/// read at different times are therefore not comparable. Two passes are made:
/// the first drives the merging to a fixpoint, the second records indices that
/// are never re-derived.
void PropertySlicing::snapshotRegions(Module &M) {
  for (unsigned pass = 0; pass < 2; ++pass) {
    memRegion.clear();
    memRegionSrc.clear();
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      for (auto &I : instructions(F)) {
        if (auto MI = dyn_cast<MemIntrinsic>(&I)) {
          unsigned len = intrinsicLength(*MI);
          bool wide = (len == std::numeric_limits<unsigned>::max());
          const Value *D = MI->getDest();
          memRegion[&I] =
              (wide || isOpaquePointer(D)) ? TOP_REGION : regions->idx(D, len);
          if (auto MT = dyn_cast<MemTransferInst>(&I)) {
            const Value *Sp = MT->getSource();
            memRegionSrc[&I] = (wide || isOpaquePointer(Sp))
                                   ? TOP_REGION
                                   : regions->idx(Sp, len);
          }
          continue;
        }
        const Value *P = nullptr;
        if (auto LI = dyn_cast<LoadInst>(&I))
          P = LI->getPointerOperand();
        else if (auto SI = dyn_cast<StoreInst>(&I))
          P = SI->getPointerOperand();
        else if (auto RMW = dyn_cast<AtomicRMWInst>(&I))
          P = RMW->getPointerOperand();
        else if (auto CX = dyn_cast<AtomicCmpXchgInst>(&I))
          P = CX->getPointerOperand();
        if (!P)
          continue;
        memRegion[&I] = isOpaquePointer(P) ? TOP_REGION : regions->idx(P);
      }
    }
  }
}

unsigned PropertySlicing::destRegion(const Instruction &I) const {
  auto it = memRegion.find(&I);
  return it == memRegion.end() ? TOP_REGION : it->second;
}

unsigned PropertySlicing::srcRegion(const Instruction &I) const {
  auto it = memRegionSrc.find(&I);
  return it == memRegionSrc.end() ? TOP_REGION : it->second;
}

/// Render why an instruction ended up relevant, as a short chain terminating
/// in whatever seeded it.
std::string PropertySlicing::explainRelevance(const Instruction *I) const {
  std::string out;
  const Instruction *cur = I;
  for (unsigned hop = 0; cur && hop < 8; ++hop) {
    if (!out.empty())
      out += " -> ";
    out += cur->getOpcodeName();
    if (auto CI = dyn_cast<CallInst>(cur))
      if (auto G = calleeOf(*CI))
        out += "(" + G->getName().str() + ")";
    if (cur != I && cur->getFunction() != I->getFunction())
      out += "@" + cur->getFunction()->getName().str();
    auto it = relevantVia.find(cur);
    if (it == relevantVia.end())
      break;
    if (it->second == cur)
      break;
    cur = it->second;
  }
  return out;
}

const Instruction *
PropertySlicing::relevanceTerminus(const Instruction *I) const {
  const Instruction *cur = I;
  for (unsigned hop = 0; cur && hop < 16; ++hop) {
    auto it = relevantVia.find(cur);
    if (it == relevantVia.end() || it->second == cur)
      break;
    cur = it->second;
  }
  return cur;
}

void PropertySlicing::markValue(const Value *V, bool &changed) {
  if (!V || isa<Constant>(V) || isa<BasicBlock>(V))
    return;
  if (relevant.insert(V).second) {
    changed = true;
    if (markSource)
      relevantVia[V] = markSource;
  }
}

/// A read whose region is TOP could have come from anywhere, so every region
/// becomes relevant -- otherwise a store the read can observe might be dropped.
void PropertySlicing::markRegionIdx(unsigned r, const Instruction &I,
                                    bool &changed) {
  if (r == TOP_REGION) {
    if (!topRelevant) {
      topRelevant = true;
      changed = true;
    }
    return;
  }
  if (relevantRegions.insert(r).second) {
    changed = true;
    if (!regionWhy.count(r))
      regionWhy[r] = I.getFunction()->getName().str();
  }
}

bool PropertySlicing::regionIsRelevant(unsigned r) const {
  return topRelevant || r == TOP_REGION || relevantRegions.count(r) > 0;
}

void PropertySlicing::seedRoots(Module &M) {
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (auto &I : instructions(F)) {
      bool isRoot = false;
      if (auto CI = dyn_cast<CallInst>(&I))
        isRoot = isPropertyRoot(*CI) || hasVerificationEffect(*CI);
      // Effects the abstraction cannot model are retained from the start.
      if (isRoot || hasUnmodelledEffect(I))
        keep.insert(&I);
    }
  }
}

void PropertySlicing::propagate(Module &M) {
  // Per-function control dependence, computed once.
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    auto &PDT = getAnalysis<PostDominatorTreeWrapperPass>(F).getPostDomTree();
    auto &ER = exitReaching[&F];
    collectExitReaching(F, ER);
    computeControlDependence(F, PDT, ER, CD[&F]);
    // Where post-dominance is undefined, retain every branch outright.
    for (auto &BB : F)
      if (!ER.count(&BB)) {
        keep.insert(BB.getTerminator());
        for (auto &Op : BB.getTerminator()->operands()) {
          bool ignored = false;
          markValue(Op.get(), ignored);
        }
      }
    for (auto &kv : CD[&F])
      cdEdges += kv.second.size();
    for (auto &BB : F)
      if (!PDT.getNode(&BB))
        pdtHoles++;
  }

  bool changed = true;
  while (changed) {
    changed = false;
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;

      for (auto &I : instructions(F)) {
        bool kept = keep.count(&I) > 0;

        if (!kept && relevant.count(&I))
          kept = true;

        if (!kept) {
          if (isa<StoreInst>(&I) || isa<MemIntrinsic>(&I) ||
              isa<AtomicRMWInst>(&I) || isa<AtomicCmpXchgInst>(&I)) {
            // A write whose region is TOP may land on any relevant object.
            if (regionIsRelevant(destRegion(I)))
              kept = true;
          } else if (auto CI = dyn_cast<CallInst>(&I)) {
            auto G = calleeOf(*CI);
            if (!G)
              // No resolvable callee: an indirect target could do anything.
              // Inline asm is the one exception under
              // -property-slicing-relax-asm, where we adopt SMACK's own
              // Stmt::skip() semantics for it.
              kept = !(CI->isInlineAsm() && PropertySlicingRelaxAsm);
            else if (mayReachError.count(G) || unsafeToDrop.count(G) ||
                     writesTop.count(G))
              kept = true;
            else {
              auto it = writtenRegions.find(G);
              if (it != writtenRegions.end())
                for (auto r : it->second)
                  if (regionIsRelevant(r))
                    kept = true;
            }
          }
        }

        if (!kept)
          continue;
        if (keep.insert(&I).second)
          changed = true;

        // A kept instruction needs its operands. For a call, marking every
        // actual wholesale is sound but very coarse: a call is frequently kept
        // only because the callee may reach the error or has an effect on some
        // other region, and then none of its arguments need be relevant. So
        // propagate per-parameter instead -- an actual becomes relevant only
        // when the corresponding formal is relevant inside the callee, which
        // ordinary intraprocedural propagation establishes. Callees without a
        // body keep the wholesale rule, since nothing can be established about
        // them.
        markSource = &I;
        auto CIforArgs = dyn_cast<CallInst>(&I);
        const Function *Gee = CIforArgs ? calleeOf(*CIforArgs) : nullptr;
        if (CIforArgs && Gee && !Gee->isDeclaration() && !Gee->isVarArg() &&
            Gee->arg_size() == CIforArgs->arg_size()) {
          unsigned k = 0;
          for (auto &A : Gee->args()) {
            if (relevant.count(&A))
              markValue(CIforArgs->getArgOperand(k), changed);
            ++k;
          }
        } else {
          for (auto &Op : I.operands())
            markValue(Op.get(), changed);
        }
        if (isa<LoadInst>(&I) || isa<AtomicRMWInst>(&I) ||
            isa<AtomicCmpXchgInst>(&I))
          markRegionIdx(destRegion(I), I, changed);
        else if (isa<MemTransferInst>(&I))
          markRegionIdx(srcRegion(I), I, changed);

        markSource = nullptr;

        // A relevant PHI depends not only on its incoming values but on
        // WHICH edge was taken, so the branches that select between them must
        // be retained. Without this the merge block is not control-dependent
        // on the deciding branch (it post-dominates it), the condition is
        // replaced by undef, and the PHI becomes nondeterministic -- sound,
        // but a false-alarm factory: it is what turned test/c/data/func_ptr.c
        // from verified into a spurious error. This is the rule the unbuilt
        // contract slicer also used (lib/smack/Slicing.cpp:159-164).
        if (auto PN = dyn_cast<PHINode>(&I)) {
          for (unsigned k = 0, e = PN->getNumIncomingValues(); k < e; ++k) {
            auto *T = PN->getIncomingBlock(k)->getTerminator();
            if (keep.insert(T).second)
              changed = true;
            for (auto &Op : T->operands())
              markValue(Op.get(), changed);
          }
        }

        // A relevant call result makes the callee's returned values relevant.
        if (auto CI = dyn_cast<CallInst>(&I)) {
          if (relevant.count(CI)) {
            if (auto G = calleeOf(*CI))
              if (!G->isDeclaration())
                for (auto &BB : *G)
                  if (auto RI = dyn_cast<ReturnInst>(BB.getTerminator()))
                    if (RI->getReturnValue()) {
                      markValue(RI->getReturnValue(), changed);
                      if (keep.insert(RI).second)
                        changed = true;
                    }
          }
        }
      }

      // Control dependence: a block holding a kept instruction needs the
      // predicates that decide whether it executes.
      auto &cd = CD[&F];
      for (auto &BB : F) {
        bool blockNeeded = false;
        for (auto &I : BB)
          if (keep.count(&I)) {
            blockNeeded = true;
            break;
          }
        if (!blockNeeded)
          continue;
        auto it = cd.find(&BB);
        if (it == cd.end())
          continue;
        for (auto *A : it->second) {
          auto *T = A->getTerminator();
          if (keep.insert(T).second)
            changed = true;
          for (auto &Op : T->operands())
            markValue(Op.get(), changed);
        }
      }

      // Returns of a function whose result someone relevant consumes are
      // handled above; a function that may reach the error keeps its returns
      // so the call graph stays traversable.
      if (mayReachError.count(&F))
        for (auto &BB : F)
          if (auto RI = dyn_cast<ReturnInst>(BB.getTerminator()))
            if (keep.insert(RI).second)
              changed = true;
    }
  }
}

// -------------------------------------------------------------- rewriting

bool PropertySlicing::removeIrrelevantInstructions(Function &F) {
  bool changed = false;
  std::vector<Instruction *> dead;

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (I.isTerminator())
        continue;
      if (keep.count(&I))
        continue;
      dead.push_back(&I);
    }
  }

  // Backward closure means a dropped instruction can only have dropped users,
  // so deleting in reverse program order leaves no dangling uses. Anything
  // that still has a use is left in place rather than risking an invalid
  // module.
  for (auto it = dead.rbegin(); it != dead.rend(); ++it) {
    Instruction *I = *it;
    if (!I->use_empty())
      continue;
    auto &S = stats[&F];
    if (isa<LoadInst>(I))
      S.loadsRemoved++;
    else if (isa<StoreInst>(I))
      S.storesRemoved++;
    else if (isa<CallInst>(I))
      S.callsRemoved++;
    I->eraseFromParent();
    changed = true;
  }

  // A branch whose condition nothing relevant depends on becomes
  // nondeterministic rather than being deleted: the CFG shape is preserved and
  // the added executions are the sound direction for reachability. This is the
  // same device the (unbuilt) contract slicer used in Slice::remove.
  for (auto &BB : F) {
    auto *T = BB.getTerminator();
    if (keep.count(T))
      continue;
    if (auto *BI = dyn_cast<BranchInst>(T)) {
      if (BI->isConditional() && !isa<UndefValue>(BI->getCondition())) {
        SDEBUG({
          errs() << "[property-slicing] " << F.getName() << ": branch made "
                 << "nondeterministic:" << *BI << "\n";
          for (auto *S : successors(&BB)) {
            unsigned k = 0;
            for (auto &I2 : *S)
              if (keep.count(&I2))
                k++;
            auto cd = CD[&F].find(S);
            errs() << "    successor keeps " << k << " instruction(s), "
                   << (cd == CD[&F].end() ? 0 : cd->second.size())
                   << " controlling block(s)\n";
          }
        });
        auto *C = BI->getCondition();
        BI->setCondition(freshNondet(C->getType(), BI));
        changed = true;
      }
    } else if (auto *SI = dyn_cast<SwitchInst>(T)) {
      if (!isa<UndefValue>(SI->getCondition()) &&
          !isa<CallInst>(SI->getCondition())) {
        SI->setCondition(freshNondet(SI->getCondition()->getType(), SI));
        changed = true;
      }
    }
  }
  return changed;
}

bool PropertySlicing::bypassIrrelevantLoops(Function &F) {
  auto &LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
  auto &S = stats[&F];
  bool changed = false;

  // Innermost-first: bypassing an inner loop can make an outer one droppable
  // on a later run, but within one run we only consider loops whose entire
  // body (including nested loops) is irrelevant.
  std::vector<Loop *> worklist(LI.begin(), LI.end());
  std::vector<Loop *> all;
  while (!worklist.empty()) {
    Loop *L = worklist.back();
    worklist.pop_back();
    all.push_back(L);
    for (Loop *Sub : *L)
      worklist.push_back(Sub);
  }

  for (Loop *L : all) {
    LoopReason reason = LoopReason::OTHER_CONSERVATIVE;
    bool droppable = true;
    std::string blocker;

    for (auto *BB : L->blocks()) {
      for (auto &I : *BB) {
        if (I.isTerminator())
          continue;
        if (hasUnmodelledEffect(I)) {
          reason = LoopReason::VOLATILE_ATOMIC;
          droppable = false;
          break;
        }
        if (keep.count(&I)) {
          // Classify by what the blocking value is ultimately needed for, not
          // by the first instruction encountered in block order -- that is
          // nearly always the induction PHI, which says nothing.
          const Instruction *T = relevanceTerminus(&I);
          if (auto CI = dyn_cast<CallInst>(T ? T : &I)) {
            auto G = calleeOf(*CI);
            if (!G)
              reason = LoopReason::UNKNOWN_CALL;
            else if (mayReachError.count(G))
              reason = LoopReason::ERROR_REACHABLE;
            else if (unsafeToDrop.count(G))
              reason = LoopReason::UNKNOWN_CALL;
            else
              reason = LoopReason::RELEVANT_REGION;
          } else if (T &&
                     (isa<StoreInst>(T) || isa<MemIntrinsic>(T) ||
                      isa<AtomicRMWInst>(T) || isa<AtomicCmpXchgInst>(T))) {
            reason = LoopReason::RELEVANT_REGION;
          } else if (T && T->isTerminator()) {
            reason = LoopReason::CONTROL;
          } else {
            reason = LoopReason::RELEVANT_SCALAR;
          }
          blocker = explainRelevance(&I);
          droppable = false;
          break;
        }
      }
      if (!droppable)
        break;
      // A kept terminator inside the loop means something downstream is
      // control-dependent on it.
      if (keep.count(BB->getTerminator()) && BB != L->getLoopLatch()) {
        reason = LoopReason::CONTROL;
        droppable = false;
        break;
      }
    }

    BasicBlock *P = L->getLoopPreheader();
    BasicBlock *E = L->getExitBlock();
    if (droppable && !P) {
      // A dedicated preheader would come from LoopSimplify, but requiring
      // LoopSimplifyID from a ModulePass crashes the legacy pass manager here.
      reason = LoopReason::NO_PREHEADER;
      droppable = false;
      blocker = "no dedicated preheader";
    } else if (droppable && !E) {
      llvm::SmallVector<BasicBlock *, 4> Ex;
      L->getExitBlocks(Ex);
      blocker = "exit blocks: " + std::to_string(Ex.size());
      // Zero exit blocks means the loop never leaves -- there is nowhere to
      // redirect the preheader to, so no bypass exists at any precision.
      reason = Ex.empty() ? LoopReason::NO_EXIT : LoopReason::MULTIPLE_EXITS;
      droppable = false;
    }

    // A value defined in the loop and used outside it loses its definition
    // when the loop goes. If any such external user is itself relevant, the
    // loop's result matters after all and the loop stays. Otherwise the escape
    // is repairable: the backward slice has already established that nothing
    // relevant reads the value, so external uses can be replaced by undef --
    // which only adds behaviours. Refusing these outright kept 28 of the 41
    // loops on he.ko.
    std::vector<Use *> escapes;
    if (droppable) {
      for (auto *BB : L->blocks()) {
        for (auto &I : *BB) {
          for (auto &U : I.uses()) {
            auto UI = dyn_cast<Instruction>(U.getUser());
            if (!UI || L->contains(UI->getParent()))
              continue;
            if (keep.count(UI)) {
              reason = LoopReason::ESCAPING_VALUE;
              blocker = std::string(I.getOpcodeName()) + " escapes to " +
                        explainRelevance(UI);
              droppable = false;
              break;
            }
            escapes.push_back(&U);
          }
          if (!droppable)
            break;
        }
        if (!droppable)
          break;
      }
    }

    // Record the loop's source line so a profile can be matched against the
    // `SMACK warning: found loop at line N` diagnostics, which are emitted by
    // LoopBoundWarnings earlier in the pipeline and therefore still describe
    // the pre-slice module.
    unsigned line = 0;
    if (auto SL = L->getStartLoc())
      line = SL.getLine();
    if (!line)
      for (auto *BB : L->blocks()) {
        for (auto &I : *BB)
          if (auto DL2 = I.getDebugLoc()) {
            line = DL2.getLine();
            break;
          }
        if (line)
          break;
      }
    S.loopReasons.push_back(
        {std::string(F.getName()) + ":" + std::to_string(line),
         droppable ? LoopReason::BYPASSED : reason});
    if (!droppable && !blocker.empty())
      S.loopBlockers.push_back(std::string(reasonName(reason)) + " | " +
                               blocker);

    if (!droppable) {
      S.loopsKept++;
      continue;
    }

    // Detach the irrelevant escaping values before the definitions go away.
    // A PHI user keeps `undef`: its incoming block may itself be one of the
    // loop blocks about to be deleted, so there is no insertion point that
    // survives the rewrite.
    for (auto *U : escapes) {
      auto *UI = dyn_cast<Instruction>(U->getUser());
      U->set(freshNondet(U->get()->getType(),
                         (UI && !isa<PHINode>(UI)) ? UI : nullptr));
    }

    // Redirect the preheader past the loop. This can add the execution that
    // skips a nonterminating loop -- sound for reachability, and recorded as
    // an over-approximation.
    auto *T = P->getTerminator();
    bool redirected = false;
    for (unsigned i = 0; i < T->getNumSuccessors(); ++i)
      if (T->getSuccessor(i) == L->getHeader()) {
        T->setSuccessor(i, E);
        redirected = true;
      }
    if (!redirected) {
      S.loopsKept++;
      continue;
    }
    // The exit block gains a new predecessor; its PHIs need an incoming value
    // for it. Nothing relevant reads them, so undef is adequate and stays on
    // the "more behaviours" side.
    for (auto &PN : E->phis())
      if (PN.getBasicBlockIndex(P) < 0)
        PN.addIncoming(freshNondet(PN.getType(), P->getTerminator()), P);

    S.loopsBypassed++;
    changed = true;
  }

  if (changed) {
    // Drops the now-unreachable loop bodies and repairs their PHI uses.
    EliminateUnreachableBlocks(F);
  }
  return changed;
}

bool PropertySlicing::rewrite(Module &M) {
  bool changed = false;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    auto &S = stats[&F];
    S.instructionsBefore = 0;
    for (auto &BB : F) {
      S.blocksBefore++;
      for (auto &I : BB) {
        (void)I;
        S.instructionsBefore++;
      }
    }
    {
      auto &LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
      std::vector<Loop *> wl(LI.begin(), LI.end());
      while (!wl.empty()) {
        Loop *L = wl.back();
        wl.pop_back();
        S.loopsBefore++;
        for (Loop *Sub : *L)
          wl.push_back(Sub);
      }
    }
    for (auto &I : instructions(F))
      if (relevant.count(&I))
        S.relevantValues++;

    if (!PropertySlicingNoLoopBypass)
      changed |= bypassIrrelevantLoops(F);
    changed |= removeIrrelevantInstructions(F);

    for (auto &BB : F) {
      S.blocksAfter++;
      for (auto &I : BB) {
        S.instructionsAfter++;
        if (isa<LoadInst>(&I))
          S.loadsRetained++;
        else if (isa<StoreInst>(&I))
          S.storesRetained++;
        else if (isa<CallInst>(&I))
          S.callsRetained++;
      }
    }
  }
  return changed;
}

// ---------------------------------------------------------------- profile

void PropertySlicing::emitProfile(Module &M) {
  if (PropertySlicingProfile.empty())
    return;
  std::error_code EC;
  raw_fd_ostream O(PropertySlicingProfile, EC, sys::fs::OF_Text);
  if (EC) {
    errs() << "SMACK warning: cannot write property-slicing profile: "
           << EC.message() << "\n";
    return;
  }
  O << "{\n  \"module\": \"" << M.getName() << "\",\n";
  O << "  \"analysis_seconds\": " << analysisSeconds << ",\n";
  O << "  \"rewrite_seconds\": " << rewriteSeconds << ",\n";
  O << "  \"regions_total\": " << regions->size() << ",\n";
  O << "  \"regions_relevant\": "
    << (topRelevant ? regions->size() : relevantRegions.size()) << ",\n";
  O << "  \"top_region_reached\": " << (topRelevant ? "true" : "false")
    << ",\n";
  {
    unsigned opaque = 0, total = 0;
    for (auto &kv : memRegion) {
      total++;
      if (kv.second == TOP_REGION)
        opaque++;
    }
    for (auto &kv : memRegionSrc) {
      total++;
      if (kv.second == TOP_REGION)
        opaque++;
    }
    O << "  \"memory_ops\": " << total << ",\n";
    O << "  \"memory_ops_opaque\": " << opaque << ",\n";
    // Naming the few accesses that force TOP is the single most useful
    // precision diagnostic: on he.ko four of 1347 of them made all 76 regions
    // relevant.
    O << "  \"opaque_sites\": [";
    bool fo = true;
    unsigned shown = 0;
    for (auto &kv : memRegion) {
      if (kv.second != TOP_REGION || shown >= 20)
        continue;
      if (!fo)
        O << ", ";
      fo = false;
      shown++;
      std::string txt;
      raw_string_ostream ss(txt);
      ss << *kv.first;
      auto t = ss.str();
      for (auto &ch : t)
        if (ch == '"' || ch == '\\')
          ch = '\'';
      if (t.size() > 160)
        t = t.substr(0, 160);
      O << "{\"fn\": \"" << kv.first->getFunction()->getName()
        << "\", \"inst\": \"" << t << "\"}";
    }
    O << "],\n";
  }
  O << "  \"functions_may_reach_error\": " << mayReachError.size() << ",\n";
  O << "  \"functions_unsafe_to_drop\": " << unsafeToDrop.size() << ",\n";
  O << "  \"control_dependence_edges\": " << cdEdges << ",\n";
  O << "  \"postdom_missing_nodes\": " << pdtHoles << ",\n";
  {
    std::map<std::string, unsigned> tally;
    for (auto &kv : unsafeWhy) {
      auto w = kv.second;
      if (w.rfind("callee:", 0) == 0)
        w = "callee";
      tally[w]++;
    }
    O << "  \"unsafe_reasons\": {";
    bool f = true;
    for (auto &kv : tally) {
      if (!f)
        O << ", ";
      f = false;
      O << "\"" << kv.first << "\": " << kv.second;
    }
    O << "},\n";
    O << "  \"region_provenance\": {";
    f = true;
    for (auto &kv : regionWhy) {
      if (!f)
        O << ", ";
      f = false;
      O << "\"" << kv.first << "\": \"" << kv.second << "\"";
    }
    O << "},\n";
  }
  O << "  \"functions\": [\n";
  bool first = true;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    auto &S = stats[&F];
    if (!first)
      O << ",\n";
    first = false;
    O << "    {\"name\": \"" << F.getName() << "\""
      << ", \"instructions_before\": " << S.instructionsBefore
      << ", \"instructions_after\": " << S.instructionsAfter
      << ", \"blocks_before\": " << S.blocksBefore
      << ", \"blocks_after\": " << S.blocksAfter
      << ", \"loops_before\": " << S.loopsBefore
      << ", \"loops_bypassed\": " << S.loopsBypassed
      << ", \"loops_kept\": " << S.loopsKept
      << ", \"relevant_values\": " << S.relevantValues
      << ", \"loads_removed\": " << S.loadsRemoved
      << ", \"loads_retained\": " << S.loadsRetained
      << ", \"stores_removed\": " << S.storesRemoved
      << ", \"stores_retained\": " << S.storesRetained
      << ", \"calls_removed\": " << S.callsRemoved
      << ", \"calls_retained\": " << S.callsRetained << ", \"loop_reasons\": [";
    bool f2 = true;
    for (auto &LR : S.loopReasons) {
      if (!f2)
        O << ", ";
      f2 = false;
      O << "{\"loop\": \"" << LR.first << "\", \"reason\": \""
        << reasonName(LR.second) << "\"}";
    }
    O << "], \"loop_blockers\": [";
    f2 = true;
    for (auto &b : S.loopBlockers) {
      if (!f2)
        O << ", ";
      f2 = false;
      auto t = b;
      for (auto &ch : t)
        if (ch == '"' || ch == '\\')
          ch = '\'';
      O << "\"" << t << "\"";
    }
    O << "]}";
  }
  O << "\n  ]\n}\n";
}

// ------------------------------------------------------------------- pass

bool propertySlicingWillRun() {
  static bool warned = false;
  if (!PropertySlicingEnabled)
    return false;

  // The over-approximation this pass performs is justified only for
  // reachability. Memory-safety and overflow properties introduce roots the
  // relevance rules above do not model, and termination is unsound by
  // construction under loop bypass.
  if (SmackOptions::MemorySafety || SmackOptions::IntegerOverflow) {
    if (!warned)
      errs() << "SMACK warning: property slicing is only sound for assertion "
                "reachability; disabling it for this property.\n";
    warned = true;
    return false;
  }

  // -fail-on-loop-exit asserts that no loop exit is reached, which is a
  // property of the *unrolled approximation* rather than of the program: a
  // "verified" verdict there means only that the bound was too small to leave
  // the loop. Slicing legitimately changes when a loop is left -- an
  // irrelevant loop may be bypassed outright -- so the two cannot both hold.
  // Measured on test/c/unroll: nine tests flip from verified to a spurious
  // error, with and without loop bypass.
  if (SmackOptions::FailOnLoopExit) {
    if (!warned)
      errs() << "SMACK warning: property slicing is incompatible with "
                "-fail-on-loop-exit, whose property depends on the unroll "
                "bound; disabling it.\n";
    warned = true;
    return false;
  }

  // --pthread. Every relevance rule in this pass is a *sequential* dependence:
  // an instruction is kept when the property's value depends on it along the
  // thread's own control flow. Under an interleaved semantics that is the
  // wrong relation in both directions.
  //
  //   - A store that no *later* instruction of this thread reads is still read
  //     by another thread. The slicer drops it, and the protocol it
  //     implemented is gone.
  //   - A loop whose exit test reads a location another thread writes carries
  //     no intra-thread control dependence -- the exit block post-dominates
  //     the header, so nothing after the loop is control-dependent on the
  //     test. bypassIrrelevantLoops therefore deletes the busy-wait, and
  //     -property-slicing-no-loop-bypass is not a remedy: the exit condition
  //     is nondeterminized instead, which lets the spin leave at any moment.
  //
  // Measured on test/c/pthread_extras with --pthread --context-bound=2:
  // peterson, dekker and szymanski all go from verified to a spurious error,
  // because both threads lose their `flag = 1` / `turn = ...` stores and their
  // spin loops and walk straight into the critical section.
  //
  // Fixing this needs a may-happen-in-parallel notion the pass does not have
  // (and cannot get cheaply: it would have to keep every store to a shared
  // region as well as every loop testing one, which on these programs is
  // everything). SMACK's concurrency model lives in string literals --
  // `__SMACK_code("async call ...")` in share/smack/lib/pthread.c -- so the
  // slicer could not even see the thread edges to be conservative about.
  if (PropertySlicingPthread) {
    if (!warned)
      errs() << "SMACK warning: property slicing models only sequential "
                "dependence and would remove thread synchronisation; "
                "disabling it for --pthread.\n";
    warned = true;
    return false;
  }

  return true;
}

/// A *distinct* nondeterministic value for each site the slicer needs one.
///
/// `undef` cannot be used here. `UndefValue::get(T)` is uniqued per type and
/// `Naming::get` caches by `Value *`, so `SmackRep` emits every undef of a
/// type as one module-global Boogie `const` (SmackRep.cpp:813-816,
/// Naming.cpp:238/269). A Boogie constant is a single unconstrained but
/// *fixed* value, so every site sharing it is forced to agree -- on one
/// sliced driver a single `const $u0: i1` was the condition of 363 branches.
/// That *removes* execution combinations, the exact opposite of the
/// over-approximation the bypass and nondeterminization rules rely on, and is
/// unsound wherever the relevance relation is imprecise.
///
/// A call to a body-less declaration is havoced by Boogie per call site, which
/// is the intended semantics. Pointer results keep `undef`: an external call
/// returning a pointer additionally gets `assume $isExternal(p)`
/// (SmackInstGenerator.cpp:811-815), which would *constrain* the value, and a
/// pointer is never a branch condition so it cannot correlate control flow.
Value *PropertySlicing::freshNondet(Type *T, Instruction *InsertBefore) {
  if (T->isPointerTy() || !InsertBefore)
    return UndefValue::get(T);

  std::string suffix;
  raw_string_ostream OS(suffix);
  T->print(OS);
  OS.flush();
  for (auto &c : suffix)
    if (!isalnum(static_cast<unsigned char>(c)))
      c = '_';

  Module *M = InsertBefore->getModule();
  FunctionCallee C =
      M->getOrInsertFunction("__SMACK_slice_nondet_" + suffix, T);
  return CallInst::Create(C, "", InsertBefore);
}

bool PropertySlicing::runOnModule(Module &M) {
  if (!propertySlicingWillRun())
    return false;

  DL = &M.getDataLayout();
  regions = &getAnalysis<Regions>();
  DSA = &getAnalysis<DSAWrapper>();

  auto T0 = std::chrono::steady_clock::now();
  // Ablation: with regions switched off every memory access is TOP, i.e. the
  // heap is a single object -- exactly the model a slicer that did NOT reuse
  // SMACK's DSA partition would have. Comparing the two answers directly how
  // much the region abstraction is actually worth here.
  topRelevant = PropertySlicingNoRegions;
  snapshotRegions(M);
  computeMayReachError(M);
  computeEffects(M);
  seedRoots(M);
  propagate(M);
  analysisSeconds = secondsSince(T0);

  auto T1 = std::chrono::steady_clock::now();
  bool changed = rewrite(M);
  rewriteSeconds = secondsSince(T1);

  SDEBUG(errs() << "[property-slicing] regions " << relevantRegions.size()
                << "/" << regions->size() << " relevant, "
                << mayReachError.size() << " functions may reach the error\n");

  emitProfile(M);
  return changed;
}

ModulePass *createPropertySlicingPass() { return new PropertySlicing(); }

char PropertySlicing::ID = 0;
static RegisterPass<PropertySlicing> X("property-slicing",
                                       "SMACK Property-Directed Slicing");

} // namespace smack
