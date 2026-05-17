//
// This file is distributed under the MIT License. See LICENSE for details.
//
// Behavioral equivalence tests for the legacy / NewPM dual-API passes
// introduced in Phase A5. For each converted pass, we run both wrappers on
// identical synthetic IR and assert the post-transform IR is identical.
//
// This guards the migration: any divergence between LegacyPM and NewPM
// wrappers caught here before it can affect the .bpl pipeline output.
//

#include "smack/AnnotateLoopExits.h"
#include "smack/BplFilePrinter.h"
#include "smack/DSAWrapperAnalysis.h"
#include "smack/Regions.h"
#include "smack/SmackModuleGenerator.h"
#include "smack/InitUndefAllocas.h"
#include "smack/IntegerOverflowChecker.h"
#include "smack/MemorySafetyChecker.h"
#include "smack/NormalizeLoops.h"
#include "smack/RewriteBitwiseOps.h"
#include "smack/SmackPipeline.h"
#include "smack/SplitAggregateValue.h"
#include "smack/VerifierCodeMetadata.h"
#include "utils/MergeGEP.h"
#include "utils/SimplifyExtractValue.h"
#include "utils/SimplifyInsertValue.h"

#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/InitializePasses.h"
#include "llvm/AsmParser/Parser.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"

#include "gtest/gtest.h"

#include <functional>
#include <memory>
#include <string>

using namespace llvm;

namespace {

// Initialize the legacy PassRegistry once so analysis passes referenced via
// AU.addRequired<...> resolve when the test code constructs a legacy PM.
struct LegacyPassRegistryInit {
  LegacyPassRegistryInit() {
    auto &R = *llvm::PassRegistry::getPassRegistry();
    llvm::initializeCore(R);
    llvm::initializeAnalysis(R);
    llvm::initializeTransformUtils(R);
  }
};
static LegacyPassRegistryInit s_legacyInit;

std::unique_ptr<Module> parseIR(LLVMContext &ctx, const char *src) {
  SMDiagnostic err;
  auto M = parseAssemblyString(src, err, ctx);
  if (!M) {
    std::string msg;
    raw_string_ostream os(msg);
    err.print("test", os);
    ADD_FAILURE() << "Failed to parse IR: " << msg;
  }
  return M;
}

std::string toString(Module &M) {
  std::string out;
  raw_string_ostream os(out);
  M.print(os, nullptr);
  return out;
}

template <typename LegacyPass, typename NewPMPass>
void expectModuleEquivalence(
    const char *irSource,
    std::function<void(legacy::PassManager &)> legacyPrereqs = {}) {
  LLVMContext ctxL;
  LLVMContext ctxN;
  auto legacyM = parseIR(ctxL, irSource);
  auto newPMM = parseIR(ctxN, irSource);
  ASSERT_TRUE(legacyM);
  ASSERT_TRUE(newPMM);

  {
    legacy::PassManager PM;
    if (legacyPrereqs) legacyPrereqs(PM);
    PM.add(new LegacyPass());
    PM.run(*legacyM);
  }
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
    MPM.addPass(NewPMPass());
    MPM.run(*newPMM, MAM);
  }

  EXPECT_EQ(toString(*legacyM), toString(*newPMM));
}

template <typename LegacyPass, typename NewPMPass>
void expectFunctionEquivalence(
    const char *irSource,
    std::function<void(legacy::PassManager &)> legacyPrereqs = {}) {
  LLVMContext ctxL;
  LLVMContext ctxN;
  auto legacyM = parseIR(ctxL, irSource);
  auto newPMM = parseIR(ctxN, irSource);
  ASSERT_TRUE(legacyM);
  ASSERT_TRUE(newPMM);

  {
    legacy::PassManager PM;
    if (legacyPrereqs) legacyPrereqs(PM);
    PM.add(new LegacyPass());
    PM.run(*legacyM);
  }
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

    FunctionPassManager FPM;
    FPM.addPass(NewPMPass());
    ModulePassManager MPM;
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
    MPM.run(*newPMM, MAM);
  }

  EXPECT_EQ(toString(*legacyM), toString(*newPMM));
}

} // namespace

// RewriteBitwiseOps: `shl i32 %x, 2` should become `mul i32 %x, 4` after both
// the legacy and NewPM wrappers, and the results must match.
TEST(NewPMEquivalence, RewriteBitwiseOpsShl) {
  constexpr const char *kIR = R"IR(
    define i32 @shl_two(i32 %x) {
      %r = shl i32 %x, 2
      ret i32 %r
    }
  )IR";
  expectModuleEquivalence<smack::RewriteBitwiseOps, smack::RewriteBitwiseOpsNewPM>(kIR);
}

TEST(NewPMEquivalence, RewriteBitwiseOpsAshr) {
  constexpr const char *kIR = R"IR(
    define i32 @ashr_three(i32 %x) {
      %r = ashr i32 %x, 3
      ret i32 %r
    }
  )IR";
  expectModuleEquivalence<smack::RewriteBitwiseOps, smack::RewriteBitwiseOpsNewPM>(kIR);
}

TEST(NewPMEquivalence, RewriteBitwiseOpsNoBitops) {
  // Module with no bitwise ops to rewrite — both wrappers must no-op identically.
  constexpr const char *kIR = R"IR(
    define i32 @identity(i32 %x) {
      ret i32 %x
    }
  )IR";
  expectModuleEquivalence<smack::RewriteBitwiseOps, smack::RewriteBitwiseOpsNewPM>(kIR);
}

TEST(NewPMEquivalence, SimplifyEVTrivial) {
  constexpr const char *kIR = R"IR(
    define i32 @ev_const() {
      %r = extractvalue { i32, i32 } { i32 7, i32 9 }, 0
      ret i32 %r
    }
  )IR";
  expectModuleEquivalence<SimplifyEV, SimplifyEVNewPM>(kIR);
}

TEST(NewPMEquivalence, SimplifyIVNoMatch) {
  constexpr const char *kIR = R"IR(
    define i32 @no_iv(i32 %x) {
      ret i32 %x
    }
  )IR";
  expectModuleEquivalence<SimplifyIV, SimplifyIVNewPM>(kIR);
}

// InitUndefAllocas needs DominatorTreeAnalysis. Both wrappers should detect
// the uninitialized load and insert a `__SMACK_nondet_int` store.
TEST(NewPMEquivalence, InitUndefAllocasUninitializedLoad) {
  constexpr const char *kIR = R"IR(
    define i32 @uninitialized() {
      %a = alloca i32
      %v = load i32, ptr %a
      ret i32 %v
    }
  )IR";
  expectFunctionEquivalence<smack::InitUndefAllocas, smack::InitUndefAllocasNewPM>(
      kIR,
      [](legacy::PassManager &PM) { PM.add(new DominatorTreeWrapperPass()); });
}

TEST(NewPMEquivalence, InitUndefAllocasDominatedLoadUnchanged) {
  // Load IS dominated by a store, so the pass should no-op identically on both paths.
  constexpr const char *kIR = R"IR(
    define i32 @initialized() {
      %a = alloca i32
      store i32 42, ptr %a
      %v = load i32, ptr %a
      ret i32 %v
    }
  )IR";
  expectFunctionEquivalence<smack::InitUndefAllocas, smack::InitUndefAllocasNewPM>(
      kIR,
      [](legacy::PassManager &PM) { PM.add(new DominatorTreeWrapperPass()); });
}

TEST(NewPMEquivalence, NormalizeLoopsSimpleLoop) {
  constexpr const char *kIR = R"IR(
    define void @loop(i32 %n) {
    entry:
      br label %hdr
    hdr:
      %i = phi i32 [ 0, %entry ], [ %i.next, %body ]
      %c = icmp slt i32 %i, %n
      br i1 %c, label %body, label %exit
    body:
      %i.next = add i32 %i, 1
      br label %hdr
    exit:
      ret void
    }
  )IR";
  expectModuleEquivalence<smack::NormalizeLoops, smack::NormalizeLoopsNewPM>(
      kIR,
      [](legacy::PassManager &PM) {
        PM.add(new DominatorTreeWrapperPass());
        PM.add(new LoopInfoWrapperPass());
      });
}

TEST(NewPMEquivalence, NormalizeLoopsNoLoops) {
  constexpr const char *kIR = R"IR(
    define i32 @noloop(i32 %x) {
      ret i32 %x
    }
  )IR";
  expectModuleEquivalence<smack::NormalizeLoops, smack::NormalizeLoopsNewPM>(
      kIR,
      [](legacy::PassManager &PM) {
        PM.add(new DominatorTreeWrapperPass());
        PM.add(new LoopInfoWrapperPass());
      });
}

TEST(NewPMEquivalence, AnnotateLoopExitsSimpleLoop) {
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_loop_exit()

    define void @loop_exit_test(i32 %n) {
    entry:
      br label %hdr
    hdr:
      %i = phi i32 [ 0, %entry ], [ %i.next, %body ]
      %c = icmp slt i32 %i, %n
      br i1 %c, label %body, label %exit
    body:
      %i.next = add i32 %i, 1
      br label %hdr
    exit:
      ret void
    }
  )IR";
  expectFunctionEquivalence<smack::AnnotateLoopExits,
                            smack::AnnotateLoopExitsNewPM>(
      kIR,
      [](legacy::PassManager &PM) {
        PM.add(new DominatorTreeWrapperPass());
        PM.add(new LoopInfoWrapperPass());
        PM.add(createLoopSimplifyPass());
      });
}

// IntegerOverflowChecker asserts that `__SMACK_check_overflow` and
// `__VERIFIER_assume` are present, so the pipeline smoke tests must declare
// them — mirrors what the real SMACK frontend links in before running the
// pipeline. Keep these decls in a single constant so both tests stay in sync.
constexpr const char *kSmackRuntimeDecls = R"IR(
  declare void @__SMACK_check_overflow(i32)
  declare void @__VERIFIER_assume(i32)
)IR";

TEST(NewPMPipeline, RunsOnTrivialModule) {
  LLVMContext ctx;
  std::string ir = std::string(kSmackRuntimeDecls) + R"IR(
    define i32 @main() {
      ret i32 0
    }
  )IR";
  auto M = parseIR(ctx, ir.c_str());
  ASSERT_TRUE(M);
  smack::SmackPipelineOptions opts;
  opts.modular = true;
  smack::runSmackTierANewPM(*M, opts);
  std::string out = toString(*M);
  EXPECT_NE(out.find("@main"), std::string::npos);
}

TEST(NewPMPipeline, RunsOnShlModule) {
  LLVMContext ctx;
  std::string ir = std::string(kSmackRuntimeDecls) + R"IR(
    define i32 @shifted(i32 %x) {
      %r = shl i32 %x, 2
      ret i32 %r
    }
  )IR";
  auto M = parseIR(ctx, ir.c_str());
  ASSERT_TRUE(M);
  smack::SmackPipelineOptions opts;
  opts.modular = true;
  smack::runSmackTierANewPM(*M, opts);
  std::string out = toString(*M);
  EXPECT_NE(out.find("@shifted"), std::string::npos);
}

TEST(NewPMEquivalence, SplitAggregateValueNoAggregate) {
  constexpr const char *kIR = R"IR(
    define i32 @scalar(i32 %x) {
      ret i32 %x
    }
  )IR";
  expectFunctionEquivalence<smack::SplitAggregateValue,
                            smack::SplitAggregateValueNewPM>(kIR);
}

TEST(NewPMEquivalence, SplitAggregateValueConstantReturn) {
  constexpr const char *kIR = R"IR(
    define { i32, i32 } @const_ret() {
      ret { i32, i32 } { i32 1, i32 2 }
    }
  )IR";
  expectFunctionEquivalence<smack::SplitAggregateValue,
                            smack::SplitAggregateValueNewPM>(kIR);
}

TEST(NewPMEquivalence, VerifierCodeMetadataPlain) {
  constexpr const char *kIR = R"IR(
    define i32 @plain(i32 %x, i32 %y) {
      %r = add i32 %x, %y
      ret i32 %r
    }
  )IR";
  expectModuleEquivalence<smack::VerifierCodeMetadata,
                          smack::VerifierCodeMetadataNewPM>(kIR);
}

TEST(NewPMEquivalence, VerifierCodeMetadataWithVerifierCall) {
  constexpr const char *kIR = R"IR(
    declare void @__VERIFIER_assume(i32)

    define void @uses_verifier(i32 %x) {
      call void @__VERIFIER_assume(i32 %x)
      ret void
    }
  )IR";
  expectModuleEquivalence<smack::VerifierCodeMetadata,
                          smack::VerifierCodeMetadataNewPM>(kIR);
}

TEST(NewPMEquivalence, MemorySafetyCheckerNoOps) {
  // Function has no loads/stores/returns-that-trigger-leak — both wrappers
  // should produce identical IR.
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_check_memory_safety(ptr, ptr)
    declare void @__SMACK_check_memory_leak()

    define i32 @const() {
      ret i32 0
    }
  )IR";
  expectFunctionEquivalence<smack::MemorySafetyChecker,
                            smack::MemorySafetyCheckerNewPM>(kIR);
}

TEST(NewPMEquivalence, MemorySafetyCheckerLoadStore) {
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_check_memory_safety(ptr, ptr)
    declare void @__SMACK_check_memory_leak()

    define void @rw(ptr %p) {
      %v = load i32, ptr %p
      store i32 %v, ptr %p
      ret void
    }
  )IR";
  expectFunctionEquivalence<smack::MemorySafetyChecker,
                            smack::MemorySafetyCheckerNewPM>(kIR);
}

TEST(NewPMEquivalence, IntegerOverflowCheckerNoIntrinsics) {
  // No overflow intrinsics or ubsan calls — both wrappers should no-op identically.
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_check_overflow(i32)
    declare void @__VERIFIER_assume(i32)

    define i32 @plain_add(i32 %x, i32 %y) {
      %r = add i32 %x, %y
      ret i32 %r
    }
  )IR";
  expectModuleEquivalence<smack::IntegerOverflowChecker,
                          smack::IntegerOverflowCheckerNewPM>(kIR);
}

TEST(NewPMEquivalence, IntegerOverflowCheckerSaddWithOverflow) {
  // Module with llvm.sadd.with.overflow.i32 — pass rewrites it into a
  // double-width add + truncation + overflow flag. Both wrappers must produce
  // byte-identical IR.
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_check_overflow(i32)
    declare void @__VERIFIER_assume(i32)
    declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32)

    define i32 @sadd_check(i32 %x, i32 %y) {
      %p = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %x, i32 %y)
      %v = extractvalue { i32, i1 } %p, 0
      ret i32 %v
    }
  )IR";
  expectModuleEquivalence<smack::IntegerOverflowChecker,
                          smack::IntegerOverflowCheckerNewPM>(kIR);
}

TEST(NewPMFullPipeline, EquivalentBplVsLegacyOnMinimalModule) {
  // Run both legacy pipeline (addSmackPreBplPasses + addSmackBplPasses) and
  // runSmackFullNewPM on identical IR. Assert .bpl outputs are byte-identical.
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_check_overflow(i32)
    declare void @__VERIFIER_assume(i32)

    define i32 @main() {
      ret i32 0
    }
  )IR";

  // Legacy run.
  std::string legacyBpl;
  {
    LLVMContext ctx;
    auto M = parseIR(ctx, kIR);
    ASSERT_TRUE(M);
    smack::SmackPipelineOptions opts;
    opts.modular = true;
    smack::runSmackPreBplPipeline(*M, opts);
    raw_string_ostream os(legacyBpl);
    legacy::PassManager PM;
    smack::SmackBplOptions bopts;
    smack::addSmackBplPasses(PM, os, bopts);
    PM.run(*M);
  }

  // NewPM run.
  std::string newpmBpl;
  {
    LLVMContext ctx;
    auto M = parseIR(ctx, kIR);
    ASSERT_TRUE(M);
    smack::SmackPipelineOptions opts;
    opts.modular = true;
    smack::SmackBplOptions bopts;
    raw_string_ostream os(newpmBpl);
    smack::runSmackFullNewPM(*M, os, opts, bopts);
  }

  // Both must be non-empty.
  EXPECT_FALSE(legacyBpl.empty());
  EXPECT_FALSE(newpmBpl.empty());
  // Both must contain procedure declarations.
  EXPECT_NE(legacyBpl.find("procedure"), std::string::npos);
  EXPECT_NE(newpmBpl.find("procedure"), std::string::npos);
  // Strict byte-equivalence on the small synthetic input. If this ever
  // diverges, sea-dsa state or pass scheduling differs between the two.
  EXPECT_EQ(legacyBpl, newpmBpl);
}

TEST(NewPMFullPipeline, PipelineReportRecordsPassTimings) {
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_check_overflow(i32)
    declare void @__VERIFIER_assume(i32)

    define i32 @main() {
      ret i32 0
    }
  )IR";

  LLVMContext ctx;
  auto M = parseIR(ctx, kIR);
  ASSERT_TRUE(M);

  std::string bpl;
  raw_string_ostream os(bpl);
  smack::SmackPipelineOptions opts;
  opts.modular = true;
  smack::SmackBplOptions bopts;
  smack::SmackPipelineReport report;
  smack::runSmackFullNewPM(*M, os, opts, bopts, &report);

  EXPECT_FALSE(bpl.empty());
  ASSERT_FALSE(report.passes.empty());
  bool sawNonSkippedPass = false;
  bool sawModulePass = false;
  for (const auto &pass : report.passes) {
    EXPECT_FALSE(pass.name.empty());
    EXPECT_FALSE(pass.irUnit.empty());
    EXPECT_GE(pass.wallMs, 0.0);
    sawNonSkippedPass |= !pass.skipped;
    sawModulePass |= pass.irUnit == "module";
  }
  EXPECT_TRUE(sawNonSkippedPass);
  EXPECT_TRUE(sawModulePass);
}

TEST(NewPMTierD, BplFilePrinterEmitsBoogieFromMinimalModule) {
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_check_overflow(i32)
    declare void @__VERIFIER_assume(i32)

    define i32 @main() {
      ret i32 0
    }
  )IR";
  LLVMContext ctx;
  auto M = parseIR(ctx, kIR);
  ASSERT_TRUE(M);

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
  MAM.registerPass([&] { return smack::DSAWrapperAnalysis(); });
  MAM.registerPass([&] { return smack::RegionsAnalysis(); });
  MAM.registerPass([&] { return smack::SmackModuleGeneratorAnalysis(); });

  std::string bplOut;
  raw_string_ostream os(bplOut);
  ModulePassManager MPM;
  MPM.addPass(smack::BplFilePrinterNewPM(os));
  MPM.run(*M, MAM);

  // Full Tier-A→B→C→D NewPM stack ran without crashing and produced bpl text.
  EXPECT_FALSE(bplOut.empty());
  EXPECT_NE(bplOut.find("procedure"), std::string::npos);
}

TEST(NewPMTierC, RegionsAnalysisRunsViaDSAWrapper) {
  constexpr const char *kIR = R"IR(
    @g = global i32 0

    define i32 @read_global() {
      %v = load i32, ptr @g
      ret i32 %v
    }

    define void @write_global(i32 %x) {
      store i32 %x, ptr @g
      ret void
    }
  )IR";
  LLVMContext ctx;
  auto M = parseIR(ctx, kIR);
  ASSERT_TRUE(M);

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
  MAM.registerPass([&] { return smack::DSAWrapperAnalysis(); });
  MAM.registerPass([&] { return smack::RegionsAnalysis(); });

  auto &regions = MAM.getResult<smack::RegionsAnalysis>(*M);
  ASSERT_NE(regions.regions.get(), nullptr);
  EXPECT_GE(regions->size(), 0u);
}

TEST(NewPMTierC, DSAWrapperAnalysisRunsOnTrivialModule) {
  constexpr const char *kIR = R"IR(
    @g = global i32 0

    define i32 @main() {
      %v = load i32, ptr @g
      ret i32 %v
    }
  )IR";
  LLVMContext ctx;
  auto M = parseIR(ctx, kIR);
  ASSERT_TRUE(M);

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
  MAM.registerPass([&] { return smack::DSAWrapperAnalysis(); });

  // Pulling the result must instantiate the legacy DSA pipeline + DSAWrapper.
  auto &result = MAM.getResult<smack::DSAWrapperAnalysis>(*M);
  ASSERT_NE(result.wrapper, nullptr);

  // Probe at least one query interface to confirm the wrapper has live state.
  auto *G = M->getGlobalVariable("g");
  ASSERT_NE(G, nullptr);
  // getNode may be nullptr for some IR shapes — accept either; the
  // important contract is that the call doesn't crash.
  (void)result.getNode(G);
}

TEST(NewPMEquivalence, MergeArrayGEPSingle) {
  constexpr const char *kIR = R"IR(
    define i32 @one_gep(ptr %p) {
      %g = getelementptr inbounds i32, ptr %p, i32 1
      %v = load i32, ptr %g
      ret i32 %v
    }
  )IR";
  expectModuleEquivalence<MergeArrayGEP, MergeArrayGEPNewPM>(kIR);
}
