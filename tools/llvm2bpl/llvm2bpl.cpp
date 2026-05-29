//
// Copyright (c) 2013 Pantazis Deligiannis (p.deligiannis@imperial.ac.uk)
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/raw_ostream.h"

#include "smack/SmackPipeline.h"

#include <chrono>
#include <functional>
#include <vector>

using namespace llvm;

static cl::opt<std::string> InputFilename(cl::Positional,
                                          cl::desc("<input LLVM bitcode file>"),
                                          cl::Required,
                                          cl::value_desc("filename"));

static cl::opt<std::string> OutputFilename("bpl",
                                           cl::desc("Output Boogie filename"),
                                           cl::init(""),
                                           cl::value_desc("filename"));

static cl::opt<std::string>
    FinalIrFilename("ll", cl::desc("Output the finally-used LLVM IR"),
                    cl::init(""), cl::value_desc("filename"));

static cl::opt<std::string> PipelineReportFilename(
    "smack-pipeline-report",
    cl::desc("Output SMACK pipeline timing and pass report as JSON"),
    cl::init(""), cl::value_desc("filename"));

static cl::opt<std::string> MemoryPartitionReportFilename(
    "smack-memory-partition-report",
    cl::desc("Output SMACK memory partitioning report as JSON"),
    cl::init(""), cl::value_desc("filename"));

static cl::opt<bool> StaticUnroll(
    "static-unroll",
    cl::desc("Use LLVM to statically unroll loops when possible"),
    cl::init(false));

static cl::opt<bool> SkipPreBpl(
    "smack-skip-pre-bpl",
    cl::desc("Input LLVM IR has already passed SMACK pre-BPL transforms"),
    cl::init(false));

static cl::opt<std::string>
    DefaultDataLayout("default-data-layout",
                      cl::desc("data layout string to use if not specified by "
                               "module"),
                      cl::init(""), cl::value_desc("layout-string"));

static cl::opt<bool> Modular(
    "modular",
    cl::desc("Enable contracts-based modular deductive verification"),
    cl::init(false));

namespace {
using Clock = std::chrono::steady_clock;

void check(std::string E) {
  if (!E.empty()) {
    if (errs().has_colors())
      errs().changeColor(raw_ostream::RED);
    errs() << E << "\n";
    if (errs().has_colors())
      errs().resetColor();
    exit(1);
  }
}

double elapsedMs(Clock::time_point start, Clock::time_point end) {
  return std::chrono::duration<double, std::milli>(end - start).count();
}

void timePhase(smack::SmackPipelineReport &report, StringRef name,
               const std::function<void()> &action) {
  const auto start = Clock::now();
  action();
  report.phases.push_back({name.str(), elapsedMs(start, Clock::now())});
}

json::Value stringOrNull(const std::string &value) {
  if (value.empty())
    return nullptr;
  return value;
}

void writePipelineReport(const smack::SmackPipelineReport &report,
                         StringRef pipeline) {
  if (PipelineReportFilename.empty())
    return;

  std::error_code EC;
  ToolOutputFile F(PipelineReportFilename.c_str(), EC, sys::fs::OF_Text);
  if (EC)
    check(EC.message());

  json::OStream J(F.os(), 2);
  J.object([&] {
    J.attribute("schema_version", 1);
    J.attribute("llvm_version", LLVM_VERSION_STRING);
    J.attribute("pipeline", pipeline);
    J.attribute("input", InputFilename);
    J.attributeObject("outputs", [&] {
      J.attribute("bpl", stringOrNull(OutputFilename));
      J.attribute("ll", stringOrNull(FinalIrFilename));
    });
    J.attributeObject("options", [&] {
      J.attribute("modular", Modular.getValue());
      J.attribute("static_unroll", StaticUnroll.getValue());
    });
    J.attributeArray("phases", [&] {
      for (const auto &phase : report.phases) {
        J.object([&] {
          J.attribute("name", phase.name);
          J.attribute("wall_ms", phase.wallMs);
        });
      }
    });
    J.attributeArray("passes", [&] {
      for (const auto &pass : report.passes) {
        J.object([&] {
          J.attribute("name", pass.name);
          J.attribute("ir_unit", pass.irUnit);
          J.attribute("wall_ms", pass.wallMs);
          J.attribute("skipped", pass.skipped);
        });
      }
    });
  });
  F.keep();
}

void writeMemoryPartitionReport(const smack::SmackMemoryPartitionReport &report,
                                StringRef pipeline) {
  if (MemoryPartitionReportFilename.empty())
    return;

  std::error_code EC;
  ToolOutputFile F(MemoryPartitionReportFilename.c_str(), EC, sys::fs::OF_Text);
  if (EC)
    check(EC.message());

  json::OStream J(F.os(), 2);
  J.object([&] {
    J.attribute("schema_version", 2);
    J.attribute("llvm_version", LLVM_VERSION_STRING);
    J.attribute("pipeline", pipeline);
    J.attribute("input", InputFilename);
    J.attribute("partitioner", report.partitioner);
    J.attribute("dsa_mode", report.dsaMode);
    J.attribute("region_count", report.regionCount);
    J.attribute("memory_access_count", report.memoryAccessCount);
    J.attribute("merge_count", report.mergeCount);
    J.attribute("late_region_count", report.lateRegionCount);
    J.attribute("oracle_access_count", report.oracleAccessCount);
    J.attribute("oracle_callsite_effect_count",
                report.oracleCallsiteEffectCount);
    J.attribute("oracle_function_effect_count",
                report.oracleFunctionEffectCount);
    J.attribute("oracle_loop_effect_count", report.oracleLoopEffectCount);
    J.attribute("oracle_indirect_call_target_count",
                report.oracleIndirectCallTargetCount);
    J.attribute("oracle_noalias_count", report.oracleNoAliasCount);
    J.attribute("oracle_may_alias_count", report.oracleMayAliasCount);
    J.attribute("oracle_fallback_count", report.oracleFallbackCount);
    J.attribute("oracle_frame_complete_count",
                report.oracleFrameCompleteCount);
    J.attribute("oracle_frame_fallback_count",
                report.oracleFrameFallbackCount);
    J.attribute("oracle_frame_excluded_map_count",
                report.oracleFrameExcludedMapCount);
    J.attribute("oracle_frame_retained_map_count",
                report.oracleFrameRetainedMapCount);
    J.attribute("svf_loop_frame_complete_count",
                report.svfLoopFrameCompleteCount);
    J.attribute("svf_loop_frame_fallback_count",
                report.svfLoopFrameFallbackCount);
    J.attribute("svf_loop_frame_invariant_count",
                report.svfLoopFrameInvariantCount);
    J.attribute("svf_loop_frame_excluded_map_count",
                report.svfLoopFrameExcludedMapCount);
    J.attribute("svf_loop_frame_retained_map_count",
                report.svfLoopFrameRetainedMapCount);
    J.attributeArray("svf_loop_candidates", [&] {
      for (const auto &candidate : report.svfLoopCandidates) {
        J.object([&] {
          J.attribute("function", candidate.function);
          J.attribute("header", candidate.header);
          J.attribute("complete", candidate.complete);
          J.attribute("preserved_map_count", candidate.preservedMapCount);
          J.attribute("retained_map_count", candidate.retainedMapCount);
          J.attribute("ref_region_count", candidate.refRegionCount);
          J.attribute("mod_region_count", candidate.modRegionCount);
          J.attribute("fallback_reason", candidate.fallbackReason);
        });
      }
    });
    J.attributeObject("regions", [&] {
      J.attribute("singleton", report.singletonCount);
      J.attribute("allocated", report.allocatedCount);
      J.attribute("bytewise", report.bytewiseCount);
      J.attribute("incomplete", report.incompleteCount);
      J.attribute("complicated", report.complicatedCount);
      J.attribute("collapsed", report.collapsedCount);
      J.attribute("typed", report.typedCount);
      J.attribute("untyped", report.untypedCount);
    });
    J.attributeArray("fallback_reasons", [&] {
      for (const auto &reason : report.fallbackReasons) {
        J.object([&] {
          J.attribute("name", reason.name);
          J.attribute("count", reason.count);
        });
      }
    });
  });
  F.keep();
}

void printFinalIr(Module &module, std::vector<ToolOutputFile *> &files) {
  if (FinalIrFilename.empty())
    return;

  std::error_code EC;
  auto F = new ToolOutputFile(FinalIrFilename.c_str(), EC, sys::fs::OF_None);
  if (EC)
    check(EC.message());
  F->keep();
  files.push_back(F);
  legacy::PassManager printPM;
  printPM.add(createPrintModulePass(F->os()));
  printPM.run(module);
}
} // namespace

int main(int argc, char **argv) {
  llvm_shutdown_obj shutdown;
  cl::ParseCommandLineOptions(
      argc, argv, "llvm2bpl - LLVM bitcode to Boogie transformation\n");

  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram PSTP(argc, argv);
  EnableDebugBuffering = true;

  LLVMContext Context;
  smack::SmackPipelineReport pipelineReport;
  smack::SmackMemoryPartitionReport memoryPartitionReport;

  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmPrinters();
  InitializeAllAsmParsers();

  SMDiagnostic err;
  std::unique_ptr<Module> module;
  timePhase(pipelineReport, "parse-ir", [&] {
    module = parseIRFile(InputFilename, err, Context);
  });
  if (!err.getMessage().empty())
    check("Problem reading input bitcode/IR: " + err.getMessage().str());

  smack::SmackPipelineOptions options;
  options.staticUnroll = StaticUnroll;
  options.modular = Modular;
  options.defaultDataLayout = DefaultDataLayout;

  std::vector<ToolOutputFile *> files;

#ifdef SMACK_NEW_PM
  // Build-time opt-in to NewPM full pipeline. Runs Tier A+B+C+D NewPM
  // siblings via PassBuilder/ModulePassManager. The Tier C analyses
  // (DSAWrapperAnalysis, RegionsAnalysis) wrap the SVF-backed DSAWrapper.
  if (!OutputFilename.empty()) {
    std::error_code EC;
    auto F = new ToolOutputFile(OutputFilename.c_str(), EC, sys::fs::OF_None);
    if (EC)
      check(EC.message());
    F->keep();
    files.push_back(F);
    smack::SmackBplOptions bopts;
    bopts.memoryPartitionReport =
        MemoryPartitionReportFilename.empty() ? nullptr : &memoryPartitionReport;
    if (SkipPreBpl) {
      timePhase(pipelineReport, "bpl-emission", [&] {
        smack::emitSmackBpl(*module, F->os(), bopts);
      });
    } else {
      timePhase(pipelineReport, "newpm-full", [&] {
        smack::runSmackFullNewPM(*module, F->os(), options, bopts,
                                 PipelineReportFilename.empty()
                                     ? nullptr
                                     : &pipelineReport);
      });
    }
  } else {
    // No output file requested — just run pre-bpl pipeline for side effects.
    if (!SkipPreBpl) {
      timePhase(pipelineReport, "pre-bpl", [&] {
        smack::runSmackPreBplPipeline(*module, options);
      });
    }
  }
  timePhase(pipelineReport, "final-ir", [&] { printFinalIr(*module, files); });
  writePipelineReport(pipelineReport, "newpm");
  writeMemoryPartitionReport(memoryPartitionReport, "newpm");
#else
  const bool noReports =
      PipelineReportFilename.empty() && MemoryPartitionReportFilename.empty();
  if (noReports) {
    legacy::PassManager passManager;
    if (!SkipPreBpl)
      smack::addSmackPreBplPasses(*module, passManager, options);

    if (!FinalIrFilename.empty()) {
      std::error_code EC;
      auto F = new ToolOutputFile(FinalIrFilename.c_str(), EC, sys::fs::OF_None);
      if (EC)
        check(EC.message());
      F->keep();
      files.push_back(F);
      passManager.add(createPrintModulePass(F->os()));
    }

    if (!OutputFilename.empty()) {
      std::error_code EC;
      auto F = new ToolOutputFile(OutputFilename.c_str(), EC, sys::fs::OF_None);
      if (EC)
        check(EC.message());
      F->keep();
      files.push_back(F);
      smack::addSmackBplPasses(passManager, F->os());
    }

    passManager.run(*module);
  } else {
    if (!SkipPreBpl) {
      timePhase(pipelineReport, "pre-bpl", [&] {
        smack::runSmackPreBplPipeline(*module, options);
      });
    }

    timePhase(pipelineReport, "final-ir", [&] {
      printFinalIr(*module, files);
    });

    if (!OutputFilename.empty()) {
      std::error_code EC;
      auto F = new ToolOutputFile(OutputFilename.c_str(), EC, sys::fs::OF_None);
      if (EC)
        check(EC.message());
      F->keep();
      files.push_back(F);
      smack::SmackBplOptions bopts;
      bopts.memoryPartitionReport = &memoryPartitionReport;
      timePhase(pipelineReport, "bpl-emission", [&] {
        smack::emitSmackBpl(*module, F->os(), bopts);
      });
    }
    writePipelineReport(pipelineReport, "legacy");
    writeMemoryPartitionReport(memoryPartitionReport, "legacy");
  }
#endif

  for (auto F : files)
    delete F;

  return 0;
}
