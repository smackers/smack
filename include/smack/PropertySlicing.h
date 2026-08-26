//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef PROPERTYSLICING_H
#define PROPERTYSLICING_H

#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include <map>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace smack {

class Regions;
class DSAWrapper;

/// A cheap, sound, property-directed slice run just before Boogie generation.
///
/// The slice is *backward* from the property root and is deliberately built on
/// analyses SMACK has already paid for: the sea-DSA-derived `Regions`
/// partition that becomes the `$M.<k>` Boogie maps, plus per-function
/// PostDominatorTree/LoopInfo. It never introduces an alias analysis of its
/// own and never assumes two Regions are disjoint beyond what `Regions::idx`
/// already guarantees.
///
/// SOUNDNESS DIRECTION. The target is reachability (SV-COMP `unreach-call`),
/// so the obligation is
///
///     Errors(original) is a subset of Errors(sliced)
///
/// i.e. the slice may add executions but must never delete a concrete
/// error-reaching one. Bypassing a property-irrelevant loop can add the
/// execution that skips a nontermination; for reachability that is the safe
/// direction. It would NOT be safe for termination, and it is not sound for
/// memory-safety or overflow properties, whose roots this pass does not model
/// -- the pass therefore refuses to run for anything but assertion checking.
class PropertySlicing : public llvm::ModulePass {
public:
  /// Why a loop was retained; reported by the profile.
  enum class LoopReason {
    ERROR_REACHABLE,
    RELEVANT_SCALAR,
    RELEVANT_REGION,
    CONTROL,
    UNKNOWN_CALL,
    VOLATILE_ATOMIC,
    DSA_COLLAPSED_REGION,
    ESCAPING_VALUE,
    NO_PREHEADER,
    MULTIPLE_EXITS,
    NO_EXIT,
    OTHER_CONSERVATIVE,
    BYPASSED,
  };

  static const char *reasonName(LoopReason R);

  struct FunctionStats {
    unsigned instructionsBefore = 0, instructionsAfter = 0;
    unsigned blocksBefore = 0, blocksAfter = 0;
    unsigned loopsBefore = 0, loopsAfter = 0;
    unsigned relevantValues = 0;
    unsigned loadsRemoved = 0, loadsRetained = 0;
    unsigned storesRemoved = 0, storesRetained = 0;
    unsigned callsRemoved = 0, callsRetained = 0;
    unsigned loopsBypassed = 0, loopsKept = 0;
    std::vector<std::pair<std::string, LoopReason>> loopReasons;
    /// For each retained loop, the instruction that blocks it and the chain
    /// back to whatever made that instruction relevant.
    std::vector<std::string> loopBlockers;
  };

  static char ID;
  PropertySlicing() : llvm::ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
  virtual bool runOnModule(llvm::Module &M) override;

private:
  Regions *regions = nullptr;
  DSAWrapper *DSA = nullptr;
  const llvm::DataLayout *DL = nullptr;

  /// Functions from which the property root is reachable in the call graph.
  std::unordered_set<const llvm::Function *> mayReachError;
  /// Functions whose body may not be elided at a call site (unknown effects,
  /// verifier semantics, volatile/atomic, or a transitively unsafe callee).
  std::unordered_set<const llvm::Function *> unsafeToDrop;
  /// Region indices that can influence the property.
  std::unordered_set<unsigned> relevantRegions;
  /// Set once a read of an un-pinned-down pointer is retained: every region
  /// then has to be treated as relevant.
  bool topRelevant = false;
  /// Region indices written by each function, transitively.
  std::unordered_map<const llvm::Function *, std::unordered_set<unsigned>>
      writtenRegions;

  /// Diagnostics: why a function is un-droppable, and which function first
  /// made a region relevant.
  std::unordered_map<const llvm::Function *, std::string> unsafeWhy;
  std::map<unsigned, std::string> regionWhy;

  std::unordered_set<const llvm::Value *> relevant;
  std::unordered_set<const llvm::Instruction *> keep;

  std::unordered_map<const llvm::Function *, FunctionStats> stats;
  double analysisSeconds = 0.0, rewriteSeconds = 0.0;
  unsigned cdEdges = 0, pdtHoles = 0;

  /// Provenance: the instruction whose operand list first made a value
  /// relevant. Walking this backwards from a loop's blocking instruction says
  /// *why* that loop survives, which the coarse LoopReason cannot.
  std::unordered_map<const llvm::Value *, const llvm::Instruction *>
      relevantVia;
  const llvm::Instruction *markSource = nullptr;
  std::string explainRelevance(const llvm::Instruction *I) const;
  /// The far end of an instruction's relevance chain -- what it is ultimately
  /// needed *for*. Classifying a loop by the head of the chain reports the
  /// induction PHI; classifying it by the terminus reports the store.
  const llvm::Instruction *relevanceTerminus(const llvm::Instruction *I) const;

  /// Per-function control dependence: block -> blocks whose branch decides
  /// whether it executes.
  std::unordered_map<const llvm::Function *,
                     std::unordered_map<const llvm::BasicBlock *,
                                        std::vector<const llvm::BasicBlock *>>>
      CD;

  /// Per-function set of blocks from which a function exit is reachable.
  std::unordered_map<const llvm::Function *,
                     std::unordered_set<const llvm::BasicBlock *>>
      exitReaching;

  bool isPropertyRoot(const llvm::CallInst &CI) const;
  bool hasVerificationEffect(const llvm::CallInst &CI) const;
  bool hasUnmodelledEffect(const llvm::Instruction &I) const;

  void computeMayReachError(llvm::Module &M);
  void computeEffects(llvm::Module &M);
  void seedRoots(llvm::Module &M);
  void propagate(llvm::Module &M);

  void markValue(const llvm::Value *V, bool &changed);
  void markRegionIdx(unsigned r, const llvm::Instruction &I, bool &changed);
  bool regionIsRelevant(unsigned r) const;
  /// Sentinel for "this access may touch any object". Regions does NOT give
  /// this to a pointer with no sea-DSA cell -- see snapshotRegions.
  static const unsigned TOP_REGION = ~0u;

  /// Region index per memory operation, frozen before any slicing decision is
  /// made. Regions::idx mutates and renumbers the partition on every call, so
  /// indices must be collected once and never re-derived.
  std::unordered_map<const llvm::Instruction *, unsigned> memRegion;
  std::unordered_map<const llvm::Instruction *, unsigned> memRegionSrc;
  /// Functions that write through a pointer whose region could not be pinned
  /// down; a call to one may write any relevant region.
  std::unordered_set<const llvm::Function *> writesTop;

  void snapshotRegions(llvm::Module &M);
  bool isOpaquePointer(const llvm::Value *Ptr) const;
  unsigned destRegion(const llvm::Instruction &I) const;
  unsigned srcRegion(const llvm::Instruction &I) const;

  bool rewrite(llvm::Module &M);
  bool removeIrrelevantInstructions(llvm::Function &F);
  bool bypassIrrelevantLoops(llvm::Function &F);

  void emitProfile(llvm::Module &M);
};

/// Whether the pass would do anything for this invocation: the flag is on and
/// the property is one the relevance relation models. llvm2bpl consults this
/// to decide whether to *schedule* the pass at all -- requiring Regions and
/// DSAWrapper is not free of side effects on the pass pipeline, so a pass that
/// would immediately return must not be added. Warns once per run when the
/// flag is given but the property rules it out.
bool propertySlicingWillRun();

llvm::ModulePass *createPropertySlicingPass();
} // namespace smack

#endif // PROPERTYSLICING_H
