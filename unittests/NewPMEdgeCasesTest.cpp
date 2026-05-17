//
// This file is distributed under the MIT License. See LICENSE for details.
//
// Edge-case tests for the NewPM siblings introduced in Phase A5.
//
// These exercise corner-case IR shapes that the synthetic equivalence tests
// in NewPMSiblingsTest.cpp don't cover: empty modules, declaration-only
// modules, single-BB functions, recursion, deep nesting, intrinsics-only,
// and SMACK-prefixed symbols. Each test runs a NewPM sibling on the IR and
// asserts the wrapper completes (no crash, no analysis failure) — behavioral
// equivalence to legacy is already covered by NewPMSiblingsTest.cpp.
//

#include "smack/AnnotateLoopExits.h"
#include "smack/InitUndefAllocas.h"
#include "smack/IntegerOverflowChecker.h"
#include "smack/MemorySafetyChecker.h"
#include "smack/NormalizeLoops.h"
#include "smack/RemoveDeadDefs.h"
#include "smack/RewriteBitwiseOps.h"
#include "smack/RustFixes.h"
#include "smack/SmackPipeline.h"
#include "smack/SplitAggregateValue.h"
#include "smack/VerifierCodeMetadata.h"
#include "utils/MergeGEP.h"
#include "utils/SimplifyExtractValue.h"
#include "utils/SimplifyInsertValue.h"

#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/AsmParser/Parser.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils.h"

#include "gtest/gtest.h"

#include <memory>
#include <string>

using namespace llvm;

namespace {

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

// Helper to construct a NewPM ModulePassManager that runs `pass` and exercise
// it on the given IR.
template <typename NewPMPass>
void runModulePassOn(const char *irSource, NewPMPass pass) {
  LLVMContext ctx;
  auto M = parseIR(ctx, irSource);
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

  ModulePassManager MPM;
  MPM.addPass(std::move(pass));
  MPM.run(*M, MAM);
}

template <typename NewPMPass>
void runFunctionPassOn(const char *irSource, NewPMPass pass) {
  LLVMContext ctx;
  auto M = parseIR(ctx, irSource);
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

  FunctionPassManager FPM;
  FPM.addPass(std::move(pass));
  ModulePassManager MPM;
  MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  MPM.run(*M, MAM);
}

} // namespace

// ---- Empty / declaration-only modules ----

TEST(NewPMEdgeCases, EmptyModuleRustFixes) {
  runFunctionPassOn("", smack::RustFixesNewPM());
}

TEST(NewPMEdgeCases, EmptyModuleRewriteBitwise) {
  runModulePassOn("", smack::RewriteBitwiseOpsNewPM());
}

TEST(NewPMEdgeCases, EmptyModuleRemoveDeadDefs) {
  runModulePassOn("", smack::RemoveDeadDefsNewPM());
}

TEST(NewPMEdgeCases, EmptyModuleNormalizeLoops) {
  runModulePassOn("", smack::NormalizeLoopsNewPM());
}

TEST(NewPMEdgeCases, DeclarationOnlyModule) {
  constexpr const char *kIR = R"IR(
    declare i32 @external(i32)
    declare void @other()
  )IR";
  runModulePassOn(kIR, smack::RewriteBitwiseOpsNewPM());
  runModulePassOn(kIR, smack::MergeArrayGEPNewPM());
  runFunctionPassOn(kIR, smack::RustFixesNewPM());
}

// ---- Single-BB functions ----

TEST(NewPMEdgeCases, SingleBBJustReturn) {
  constexpr const char *kIR = R"IR(
    define i32 @ret_const() {
      ret i32 0
    }
  )IR";
  runModulePassOn(kIR, smack::NormalizeLoopsNewPM());
  runFunctionPassOn(kIR, smack::InitUndefAllocasNewPM());
  runFunctionPassOn(kIR, smack::SplitAggregateValueNewPM());
}

TEST(NewPMEdgeCases, SingleBBWithAlloca) {
  constexpr const char *kIR = R"IR(
    define i32 @one_alloca() {
      %a = alloca i32
      store i32 42, ptr %a
      %v = load i32, ptr %a
      ret i32 %v
    }
  )IR";
  runFunctionPassOn(kIR, smack::InitUndefAllocasNewPM());
}

// ---- Recursion ----

TEST(NewPMEdgeCases, SelfRecursiveFunction) {
  constexpr const char *kIR = R"IR(
    define i32 @factorial(i32 %n) {
    entry:
      %z = icmp eq i32 %n, 0
      br i1 %z, label %base, label %rec
    base:
      ret i32 1
    rec:
      %m = sub i32 %n, 1
      %r = call i32 @factorial(i32 %m)
      %p = mul i32 %n, %r
      ret i32 %p
    }
  )IR";
  runModulePassOn(kIR, smack::NormalizeLoopsNewPM());
  runFunctionPassOn(kIR, smack::InitUndefAllocasNewPM());
}

// ---- Deeply nested loops ----

TEST(NewPMEdgeCases, NestedLoopsNormalize) {
  constexpr const char *kIR = R"IR(
    define void @nested(i32 %n) {
    entry:
      br label %outer_hdr
    outer_hdr:
      %i = phi i32 [ 0, %entry ], [ %i.next, %outer_latch ]
      %co = icmp slt i32 %i, %n
      br i1 %co, label %inner_pre, label %exit
    inner_pre:
      br label %inner_hdr
    inner_hdr:
      %j = phi i32 [ 0, %inner_pre ], [ %j.next, %inner_body ]
      %ci = icmp slt i32 %j, %n
      br i1 %ci, label %inner_body, label %outer_latch
    inner_body:
      %j.next = add i32 %j, 1
      br label %inner_hdr
    outer_latch:
      %i.next = add i32 %i, 1
      br label %outer_hdr
    exit:
      ret void
    }
  )IR";
  runModulePassOn(kIR, smack::NormalizeLoopsNewPM());
}

TEST(NewPMEdgeCases, NestedLoopsAnnotateExits) {
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_loop_exit()

    define void @nested_exits(i32 %n) {
    entry:
      br label %outer_hdr
    outer_hdr:
      %i = phi i32 [ 0, %entry ], [ %i.next, %outer_latch ]
      %co = icmp slt i32 %i, %n
      br i1 %co, label %inner_pre, label %exit
    inner_pre:
      br label %inner_hdr
    inner_hdr:
      %j = phi i32 [ 0, %inner_pre ], [ %j.next, %inner_body ]
      %ci = icmp slt i32 %j, %n
      br i1 %ci, label %inner_body, label %outer_latch
    inner_body:
      %j.next = add i32 %j, 1
      br label %inner_hdr
    outer_latch:
      %i.next = add i32 %i, 1
      br label %outer_hdr
    exit:
      ret void
    }
  )IR";
  runFunctionPassOn(kIR, smack::AnnotateLoopExitsNewPM());
}

// ---- SMACK-prefixed functions should be skipped ----

TEST(NewPMEdgeCases, SmackPrefixedFunctionsSkipped) {
  // IntegerOverflowChecker should not touch __SMACK_* functions.
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_check_overflow(i32)
    declare void @__VERIFIER_assume(i32)

    define void @__SMACK_internal(i32 %x) {
      %r = add i32 %x, 1
      ret void
    }

    define i32 @user_fn(i32 %x) {
      %r = add i32 %x, 1
      ret i32 %r
    }
  )IR";
  runModulePassOn(kIR, smack::IntegerOverflowCheckerNewPM());
  runModulePassOn(kIR, smack::RewriteBitwiseOpsNewPM());
}

// ---- Non-integer alloca should be ignored by InitUndefAllocas ----

TEST(NewPMEdgeCases, NonIntegerAllocaIgnored) {
  constexpr const char *kIR = R"IR(
    define void @float_alloca() {
      %a = alloca float
      %v = load float, ptr %a
      ret void
    }
  )IR";
  runFunctionPassOn(kIR, smack::InitUndefAllocasNewPM());
}

TEST(NewPMEdgeCases, ArrayAllocaIgnored) {
  constexpr const char *kIR = R"IR(
    define void @array_alloca() {
      %a = alloca [4 x i32]
      ret void
    }
  )IR";
  runFunctionPassOn(kIR, smack::InitUndefAllocasNewPM());
}

// ---- Pipeline-level: full Tier A pipeline on edge cases ----

TEST(NewPMEdgeCases, PipelineOnEmptyMain) {
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
  smack::SmackPipelineOptions opts;
  opts.modular = true;
  smack::runSmackTierANewPM(*M, opts);
  std::string out;
  raw_string_ostream os(out);
  M->print(os, nullptr);
  EXPECT_NE(out.find("@main"), std::string::npos);
}

TEST(NewPMEdgeCases, PipelineOnRecursion) {
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_check_overflow(i32)
    declare void @__VERIFIER_assume(i32)

    define i32 @rec(i32 %n) {
    entry:
      %z = icmp eq i32 %n, 0
      br i1 %z, label %base, label %step
    base:
      ret i32 0
    step:
      %m = sub i32 %n, 1
      %r = call i32 @rec(i32 %m)
      %s = add i32 %r, 1
      ret i32 %s
    }
  )IR";
  LLVMContext ctx;
  auto M = parseIR(ctx, kIR);
  ASSERT_TRUE(M);
  smack::SmackPipelineOptions opts;
  opts.modular = true;
  smack::runSmackTierANewPM(*M, opts);
  std::string out;
  raw_string_ostream os(out);
  M->print(os, nullptr);
  EXPECT_NE(out.find("@rec"), std::string::npos);
}

TEST(NewPMEdgeCases, PipelineOnMultipleFunctions) {
  constexpr const char *kIR = R"IR(
    declare void @__SMACK_check_overflow(i32)
    declare void @__VERIFIER_assume(i32)

    define i32 @helper(i32 %x) {
      %r = mul i32 %x, 2
      ret i32 %r
    }

    define i32 @main() {
      %r = call i32 @helper(i32 21)
      ret i32 %r
    }
  )IR";
  LLVMContext ctx;
  auto M = parseIR(ctx, kIR);
  ASSERT_TRUE(M);
  smack::SmackPipelineOptions opts;
  opts.modular = true;
  smack::runSmackTierANewPM(*M, opts);
  std::string out;
  raw_string_ostream os(out);
  M->print(os, nullptr);
  EXPECT_NE(out.find("@main"), std::string::npos);
  EXPECT_NE(out.find("@helper"), std::string::npos);
}
