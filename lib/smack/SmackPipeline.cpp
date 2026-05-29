//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "smack-pipeline"

#include "smack/SmackPipeline.h"

#include "llvm/ADT/Any.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LazyCallGraph.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassInstrumentation.h"
#include "llvm/IR/PassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/IPO/GlobalDCE.h"
#include "llvm/Transforms/IPO/Internalize.h"
#include "llvm/Transforms/Scalar/DCE.h"
#include "llvm/Transforms/Scalar/LoopUnrollPass.h"
#include "llvm/Transforms/Utils/LCSSA.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils/LowerSwitch.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"

#include "smack/AddTiming.h"
#include "smack/DSAWrapperAnalysis.h"
#include "smack/Regions.h"
#include "utils/Devirt.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "smack/AnnotateLoopExits.h"
#include "smack/BplFilePrinter.h"
#include "smack/CodifyStaticInits.h"
#include "smack/ExtractContracts.h"
#include "smack/InitializePasses.h"
#include "smack/InitUndefAllocas.h"
#include "smack/LlvmCompat.h"
#include "smack/IntegerOverflowChecker.h"
#include "smack/MemorySafetyChecker.h"
#include "smack/Naming.h"
#include "smack/NormalizeLoops.h"
#include "smack/RemoveDeadDefs.h"
#include "smack/RewriteBitwiseOps.h"
#include "smack/RustFixes.h"
#include "smack/SimplifyLibCalls.h"
#include "smack/SmackModuleGenerator.h"
#include "smack/SmackOptions.h"
#include "smack/SmackWarnings.h"
#include "smack/SplitAggregateValue.h"
#include "smack/VerifierCodeMetadata.h"
#include "utils/InitializePasses.h"
#include "utils/MergeGEP.h"
#include "utils/SimplifyExtractValue.h"
#include "utils/SimplifyInsertValue.h"

#include <chrono>
#include <memory>
#include <vector>

using namespace llvm;

namespace llvm {
void initializeRegionsPass(PassRegistry &);
} // namespace llvm

namespace smack {
namespace {

using Clock = std::chrono::steady_clock;

double elapsedMs(Clock::time_point start, Clock::time_point end) {
  return std::chrono::duration<double, std::milli>(end - start).count();
}

std::string irUnitName(Any ir) {
  if (any_cast<const Module *>(&ir))
    return "module";
  if (any_cast<const Function *>(&ir))
    return "function";
  if (any_cast<const Loop *>(&ir))
    return "loop";
  if (any_cast<const LazyCallGraph::SCC *>(&ir))
    return "cgscc";
  return "unknown";
}

class NewPMPassTimer {
  struct ActivePass {
    std::string name;
    std::string irUnit;
    Clock::time_point start;
  };

  SmackPipelineReport &report;
  std::vector<ActivePass> active;

public:
  explicit NewPMPassTimer(SmackPipelineReport &report) : report(report) {}

  void registerCallbacks(PassInstrumentationCallbacks &callbacks) {
    callbacks.registerBeforeNonSkippedPassCallback(
        [this](StringRef passName, Any ir) {
          active.push_back({passName.str(), irUnitName(ir), Clock::now()});
        });
    callbacks.registerBeforeSkippedPassCallback(
        [this](StringRef passName, Any ir) {
          report.passes.push_back(
              {passName.str(), irUnitName(ir), 0.0, true});
        });
    callbacks.registerAfterPassCallback(
        [this](StringRef passName, Any, const PreservedAnalyses &) {
          finish(passName);
        });
    callbacks.registerAfterPassInvalidatedCallback(
        [this](StringRef passName, const PreservedAnalyses &) {
          finish(passName);
        });
  }

private:
  void finish(StringRef passName) {
    const auto end = Clock::now();
    if (active.empty()) {
      report.passes.push_back({passName.str(), "unknown", 0.0, false});
      return;
    }

    ActivePass pass = std::move(active.back());
    active.pop_back();
    report.passes.push_back(
        {std::move(pass.name), std::move(pass.irUnit),
         elapsedMs(pass.start, end), false});
  }
};

TargetMachine *getTargetMachine(Triple TheTriple, StringRef CPUStr,
                                StringRef FeaturesStr,
                                const TargetOptions &Options) {
  std::string Error;
  const std::string MArch;

  const Target *TheTarget =
      TargetRegistry::lookupTarget(MArch, TheTriple, Error);

  assert(TheTarget &&
         "If we don't have a target machine, can't do timing analysis");

  return TheTarget->createTargetMachine(
      TheTriple, CPUStr, FeaturesStr, Options, Reloc::Static, std::nullopt,
      CodeGenOptLevel::None);
}

void configureModule(Module &module, const SmackPipelineOptions &options) {
  if (module.getDataLayoutStr().empty())
    module.setDataLayout(options.defaultDataLayout);
  // The memory-region partition is now produced unconditionally by the
  // SVF-Andersen-backed DSAWrapper; there is no partitioner selection knob.
}

} // namespace

void initializeSmackPipelinePasses() {
  PassRegistry &Registry = *PassRegistry::getPassRegistry();
  initializeAnalysis(Registry);

  initializeCodifyStaticInitsPass(Registry);
  initializeDevirtualizePass(Registry);
  initializeRegionsPass(Registry);
  initializeSmackModuleGeneratorPass(Registry);
  initializeBplFilePrinterPass(Registry);
}

void addSmackPreBplPasses(Module &module, legacy::PassManager &passManager,
                          const SmackPipelineOptions &options) {
  configureModule(module, options);
  initializeSmackPipelinePasses();

  // RustFixes + the non-modular internalize/GlobalDCE/DCE cleanup run here as a
  // one-shot NewPM step rather than as legacy passes. LLVM 21 dropped the legacy
  // createGlobalDCEPass() factory (only the NewPM GlobalDCEPass survives), so the
  // cleanup can no longer be expressed in the legacy PassManager. Running it
  // immediately (before the legacy PM that emits the rest of the pipeline) keeps
  // the original ordering: RustFixes, then internalize -> GlobalDCE -> DCE ->
  // GlobalDCE -> DCE, then RemoveDeadDefs + the remaining legacy passes.
  {
    LoopAnalysisManager LAM;
    FunctionAnalysisManager FAM;
    CGSCCAnalysisManager CGAM;
    ModuleAnalysisManager MAM;
    PassBuilder PB;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    ModulePassManager MPM;
    {
      // This runs before DSA because some Rust functions cause problems.
      FunctionPassManager FPM;
      FPM.addPass(RustFixesNewPM());
      MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
    }

    if (!options.modular) {
      auto PreserveKeyGlobals = [=](const GlobalValue &GV) {
        auto name = GV.getName();
        return SmackOptions::isEntryPoint(name) || Naming::isSmackName(name) ||
               name.find("__VERIFIER_assume") != StringRef::npos;
      };
      MPM.addPass(InternalizePass(PreserveKeyGlobals));
      MPM.addPass(GlobalDCEPass());
      MPM.addPass(createModuleToFunctionPassAdaptor(DCEPass()));
      MPM.addPass(GlobalDCEPass());
      MPM.addPass(createModuleToFunctionPassAdaptor(DCEPass()));
    }

    MPM.run(module, MAM);
  }

  if (!options.modular)
    passManager.add(makePass<RemoveDeadDefs>());

  passManager.add(makePass<InitUndefAllocas>());
  passManager.add(createLowerSwitchPass());
  passManager.add(createPromoteMemoryToRegisterPass());

  if (options.staticUnroll) {
    passManager.add(createLoopSimplifyPass());
    passManager.add(createLoopUnrollPass(32767));
  }

  passManager.add(makePass<NormalizeLoops>());
  if (SmackOptions::FailOnLoopExit)
    passManager.add(makePass<AnnotateLoopExits>());
  passManager.add(makePass<SimplifyEV>());
  passManager.add(makePass<SimplifyIV>());
  passManager.add(makePass<ExtractContracts>());
  passManager.add(makePass<VerifierCodeMetadata>());
  passManager.add(createDeadCodeEliminationPass());
  passManager.add(createCodifyStaticInitsPass());
  if (!options.modular)
    passManager.add(makePass<RemoveDeadDefs>());
  passManager.add(makePass<MergeArrayGEP>());
  // Devirtualize indirect calls SVF resolves completely (must run after
  // DSAWrapper, which builds the SVF analysis it reuses; enforced via
  // Devirtualize::getAnalysisUsage requiring DSAWrapper).
  if (!SmackOptions::SkipDevirt)
    passManager.add(makePass<Devirtualize>());
  passManager.add(makePass<SplitAggregateValue>());

  if (SmackOptions::MemorySafety)
    passManager.add(makePass<MemorySafetyChecker>());

  passManager.add(makePass<IntegerOverflowChecker>());

  if (SmackOptions::RewriteBitwiseOps &&
      !(SmackOptions::BitPrecise || SmackOptions::BitPrecisePointers))
    passManager.add(makePass<RewriteBitwiseOps>());

  if (SmackOptions::AddTiming) {
    Triple ModuleTriple(module.getTargetTriple());
    assert(
        ModuleTriple.getArch() &&
        "Module has no defined architecture: unable to add timing annotations");

    const TargetOptions Options;
    std::string CPUStr = "";
    std::string FeaturesStr = "";
    TargetMachine *Machine =
        getTargetMachine(ModuleTriple, CPUStr, FeaturesStr, Options);

    assert(Machine &&
           "Module did not have a Target Machine: Cannot set up timing pass");
    TargetLibraryInfoImpl TLII(ModuleTriple);
    passManager.add(makePass<TargetLibraryInfoWrapperPass>(TLII));
    passManager.add(createTargetTransformInfoWrapperPass(
        Machine->getTargetIRAnalysis()));
    passManager.add(makePass<AddTiming>());
  }
}

void addSmackBplPasses(legacy::PassManager &passManager, raw_ostream &out,
                       const SmackBplOptions &options) {
  initializeSmackPipelinePasses();
  passManager.add(makePass<SmackModuleGenerator>(
      options.structuredLoops, options.structuredLoopsStrict,
      options.memoryPartitionReport));
  passManager.add(makePass<BplFilePrinter>(out));
}

void runSmackTierANewPM(Module &module, const SmackPipelineOptions &options) {
  configureModule(module, options);

  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;
  PassBuilder PB;
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  ModulePassManager MPM;

  // RustFixes (FunctionPass): runs before DSA because some Rust functions
  // cause problems. Mirrors the legacy order at the top of addSmackPreBplPasses.
  {
    FunctionPassManager FPM;
    FPM.addPass(RustFixesNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  if (!options.modular) {
    MPM.addPass(RemoveDeadDefsNewPM());
  }

  // InitUndefAllocas needs DominatorTree (registered above).
  {
    FunctionPassManager FPM;
    FPM.addPass(InitUndefAllocasNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  MPM.addPass(NormalizeLoopsNewPM());

  // AnnotateLoopExits is opt-in (SmackOptions::FailOnLoopExit). Mirror that gate.
  if (SmackOptions::FailOnLoopExit) {
    FunctionPassManager FPM;
    FPM.addPass(AnnotateLoopExitsNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  MPM.addPass(SimplifyEVNewPM());
  MPM.addPass(SimplifyIVNewPM());

  MPM.addPass(VerifierCodeMetadataNewPM());

  if (!options.modular) {
    MPM.addPass(RemoveDeadDefsNewPM());
  }
  MPM.addPass(MergeArrayGEPNewPM());
  // Devirtualize indirect calls (NewPM parity; DSAWrapperAnalysis, registered
  // above, builds the SVF analysis it reuses).
  if (!SmackOptions::SkipDevirt)
    MPM.addPass(llvm::DevirtualizeNewPM());

  {
    FunctionPassManager FPM;
    FPM.addPass(SplitAggregateValueNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  if (SmackOptions::MemorySafety) {
    FunctionPassManager FPM;
    FPM.addPass(MemorySafetyCheckerNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  MPM.addPass(IntegerOverflowCheckerNewPM());

  if (SmackOptions::AddTiming) {
    // TTI analysis is registered by the FAM at the top of this function.
    FunctionPassManager FPM;
    FPM.addPass(AddTimingNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  if (SmackOptions::RewriteBitwiseOps &&
      !(SmackOptions::BitPrecise || SmackOptions::BitPrecisePointers)) {
    MPM.addPass(RewriteBitwiseOpsNewPM());
  }

  MPM.run(module, MAM);
}

void addSmackBplPasses(legacy::PassManager &passManager, raw_ostream &out) {
  addSmackBplPasses(passManager, out, SmackBplOptions{});
}

void runSmackPreBplPipeline(Module &module,
                            const SmackPipelineOptions &options) {
  legacy::PassManager passManager;
  addSmackPreBplPasses(module, passManager, options);
  passManager.run(module);
}

// Full NewPM path mirrors the legacy pre-BPL ordering, including the stock
// LLVM cleanup/lowering passes before sea-dsa-sensitive SMACK passes. Keep this
// opt-in until corpus-level legacy-vs-NewPM BPL equivalence remains green in CI.
void runSmackFullNewPM(Module &module, raw_ostream &out,
                       const SmackPipelineOptions &options,
                       const SmackBplOptions &bplOptions) {
  runSmackFullNewPM(module, out, options, bplOptions, nullptr);
}

void runSmackFullNewPM(Module &module, raw_ostream &out,
                       const SmackPipelineOptions &options,
                       const SmackBplOptions &bplOptions,
                       SmackPipelineReport *report) {
  configureModule(module, options);

  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;
  PassInstrumentationCallbacks PIC;
  std::unique_ptr<NewPMPassTimer> passTimer;
  PassInstrumentationCallbacks *PICPtr = nullptr;
  if (report != nullptr) {
    passTimer = std::make_unique<NewPMPassTimer>(*report);
    passTimer->registerCallbacks(PIC);
    PICPtr = &PIC;
  }
  PassBuilder PB(nullptr, PipelineTuningOptions(), std::nullopt, PICPtr);
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  // Tier C/D analyses: SVF-backed DSAWrapper + Regions bridges.
  MAM.registerPass([&] { return DSAWrapperAnalysis(); });
  MAM.registerPass([&] { return RegionsAnalysis(); });
  MAM.registerPass([&] {
    return SmackModuleGeneratorAnalysis(bplOptions.memoryPartitionReport);
  });

  ModulePassManager MPM;

  // Tier A leaves
  {
    FunctionPassManager FPM;
    FPM.addPass(RustFixesNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // H1: stock LLVM transforms that legacy addSmackPreBplPasses runs before
  // sea-dsa. Without these, NewPM full pipeline sees un-transformed IR and
  // produces a different DSA partition (e.g. simple.c 47 vs 2 regions).
  if (!options.modular) {
    auto PreserveKeyGlobals = [=](const GlobalValue &GV) {
      auto name = GV.getName();
      return SmackOptions::isEntryPoint(name) || Naming::isSmackName(name) ||
             name.find("__VERIFIER_assume") != StringRef::npos;
    };
    MPM.addPass(InternalizePass(PreserveKeyGlobals));
    MPM.addPass(GlobalDCEPass());
    MPM.addPass(createModuleToFunctionPassAdaptor(DCEPass()));
    MPM.addPass(GlobalDCEPass());
    MPM.addPass(createModuleToFunctionPassAdaptor(DCEPass()));
    MPM.addPass(RemoveDeadDefsNewPM());
  }
  {
    FunctionPassManager FPM;
    FPM.addPass(InitUndefAllocasNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  {
    FunctionPassManager FPM;
    FPM.addPass(LowerSwitchPass());
    FPM.addPass(PromotePass()); // mem2reg
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  if (options.staticUnroll) {
    FunctionPassManager FPM;
    LoopPassManager LPM;
    FPM.addPass(LoopSimplifyPass());
    LPM.addPass(LoopFullUnrollPass());
    FPM.addPass(createFunctionToLoopPassAdaptor(std::move(LPM)));
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  MPM.addPass(NormalizeLoopsNewPM());
  if (SmackOptions::FailOnLoopExit) {
    FunctionPassManager FPM;
    FPM.addPass(AnnotateLoopExitsNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }
  MPM.addPass(SimplifyEVNewPM());
  MPM.addPass(SimplifyIVNewPM());

  // Tier B
  MPM.addPass(ExtractContractsNewPM());
  MPM.addPass(VerifierCodeMetadataNewPM());

  // Mirrors legacy: createDeadCodeEliminationPass() after VerifierCodeMetadata
  // and before CodifyStaticInits. Drops smack.c arithmetic helpers that are
  // marked unreachable after verifier metadata pass. Without this, NewPM
  // pipeline emits ~220 extra Boogie statements vs legacy.
  MPM.addPass(createModuleToFunctionPassAdaptor(DCEPass()));

  // Tier C — DSA-dependent
  MPM.addPass(CodifyStaticInitsNewPM());
  if (!options.modular)
    MPM.addPass(RemoveDeadDefsNewPM());
  MPM.addPass(MergeArrayGEPNewPM());
  {
    FunctionPassManager FPM;
    FPM.addPass(SplitAggregateValueNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }
  if (SmackOptions::MemorySafety) {
    FunctionPassManager FPM;
    FPM.addPass(MemorySafetyCheckerNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }
  MPM.addPass(IntegerOverflowCheckerNewPM());
  if (SmackOptions::AddTiming) {
    FunctionPassManager FPM;
    FPM.addPass(AddTimingNewPM());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  }
  if (SmackOptions::RewriteBitwiseOps &&
      !(SmackOptions::BitPrecise || SmackOptions::BitPrecisePointers))
    MPM.addPass(RewriteBitwiseOpsNewPM());

  // Tier D sink: emit Boogie.
  MPM.addPass(BplFilePrinterNewPM(out));

  MPM.run(module, MAM);
}

void emitSmackBpl(Module &module, raw_ostream &out,
                  const SmackBplOptions &options) {
  legacy::PassManager passManager;
  addSmackBplPasses(passManager, out, options);
  passManager.run(module);
}

void emitSmackBpl(Module &module, raw_ostream &out) {
  emitSmackBpl(module, out, SmackBplOptions{});
}

} // namespace smack
