//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef SMACK_SMACKPIPELINE_H
#define SMACK_SMACKPIPELINE_H

#include <string>
#include <vector>

namespace llvm {
class Module;
namespace legacy {
class PassManager;
} // namespace legacy
class raw_ostream;
} // namespace llvm

namespace smack {

struct SmackMemoryPartitionReport;

struct SmackPipelineOptions {
  bool staticUnroll = false;
  bool modular = false;
  std::string defaultDataLayout;
};

struct SmackBplOptions {
  bool structuredLoops = false;
  bool structuredLoopsStrict = false;
  SmackMemoryPartitionReport *memoryPartitionReport = nullptr;
};

struct SmackMemoryPartitionReport {
  struct ReasonCount {
    std::string name;
    unsigned count = 0;
  };
  struct SVFLoopCandidate {
    std::string function;
    std::string header;
    bool complete = false;
    unsigned preservedMapCount = 0;
    unsigned retainedMapCount = 0;
    unsigned refRegionCount = 0;
    unsigned modRegionCount = 0;
    std::string fallbackReason;
  };

  std::string partitioner;
  std::string dsaMode;
  unsigned regionCount = 0;
  unsigned memoryAccessCount = 0;
  unsigned mergeCount = 0;
  unsigned lateRegionCount = 0;
  unsigned singletonCount = 0;
  unsigned allocatedCount = 0;
  unsigned bytewiseCount = 0;
  unsigned incompleteCount = 0;
  unsigned complicatedCount = 0;
  unsigned collapsedCount = 0;
  unsigned typedCount = 0;
  unsigned untypedCount = 0;
  unsigned oracleAccessCount = 0;
  unsigned oracleCallsiteEffectCount = 0;
  unsigned oracleFunctionEffectCount = 0;
  unsigned oracleLoopEffectCount = 0;
  unsigned oracleIndirectCallTargetCount = 0;
  unsigned oracleNoAliasCount = 0;
  unsigned oracleMayAliasCount = 0;
  unsigned oracleFallbackCount = 0;
  unsigned oracleFrameCompleteCount = 0;
  unsigned oracleFrameFallbackCount = 0;
  unsigned oracleFrameExcludedMapCount = 0;
  unsigned oracleFrameRetainedMapCount = 0;
  unsigned svfLoopFrameCompleteCount = 0;
  unsigned svfLoopFrameFallbackCount = 0;
  unsigned svfLoopFrameInvariantCount = 0;
  unsigned svfLoopFrameExcludedMapCount = 0;
  unsigned svfLoopFrameRetainedMapCount = 0;
  std::vector<ReasonCount> fallbackReasons;
  std::vector<SVFLoopCandidate> svfLoopCandidates;
};

struct SmackPipelineReport {
  struct PhaseTiming {
    std::string name;
    double wallMs = 0.0;
  };

  struct PassTiming {
    std::string name;
    std::string irUnit;
    double wallMs = 0.0;
    bool skipped = false;
  };

  std::vector<PhaseTiming> phases;
  std::vector<PassTiming> passes;
};

void initializeSmackPipelinePasses();

void addSmackPreBplPasses(llvm::Module &module,
                          llvm::legacy::PassManager &passManager,
                          const SmackPipelineOptions &options);

void addSmackBplPasses(llvm::legacy::PassManager &passManager,
                       llvm::raw_ostream &out);
void addSmackBplPasses(llvm::legacy::PassManager &passManager,
                       llvm::raw_ostream &out,
                       const SmackBplOptions &options);

void runSmackPreBplPipeline(llvm::Module &module,
                            const SmackPipelineOptions &options);

// NewPM-based partial pipeline using the Tier-A passes ported in Phase A5.
// Runs the 9 dual-API leaves (RustFixes, RemoveDeadDefs, InitUndefAllocas,
// NormalizeLoops, AnnotateLoopExits if applicable, RewriteBitwiseOps,
// MergeArrayGEP, SimplifyEV, SimplifyIV) via PassBuilder/ModulePassManager.
// Not yet a replacement for runSmackPreBplPipeline — the analysis-heavy and
// DSA-dependent passes (Devirtualize, ExtractContracts, IntegerOverflowChecker,
// SmackModuleGenerator, etc.) still need NewPM siblings. Gated for opt-in use.
void runSmackTierANewPM(llvm::Module &module,
                        const SmackPipelineOptions &options);

// Full NewPM pipeline: Tier A + B + C + D siblings composed into a single
// ModulePassManager via PassBuilder. Tier C/D analyses bridge sea-dsa
// (legacy) via DSAWrapperAnalysis / RegionsAnalysis / SmackModuleGeneratorAnalysis.
// Emits Boogie to `out`. Gated by -DSMACK_NEW_PM=ON in tools/llvm2bpl/llvm2bpl.cpp.
void runSmackFullNewPM(llvm::Module &module, llvm::raw_ostream &out,
                       const SmackPipelineOptions &options,
                       const SmackBplOptions &bplOptions);
void runSmackFullNewPM(llvm::Module &module, llvm::raw_ostream &out,
                       const SmackPipelineOptions &options,
                       const SmackBplOptions &bplOptions,
                       SmackPipelineReport *report);

void emitSmackBpl(llvm::Module &module, llvm::raw_ostream &out);
void emitSmackBpl(llvm::Module &module, llvm::raw_ostream &out,
                  const SmackBplOptions &options);

} // namespace smack

#endif
