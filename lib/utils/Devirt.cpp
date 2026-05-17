//===- Devirt.cpp - Devirtualize using the sig match intrinsic in llva ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "devirt"

#include "utils/Devirt.h"
#include "smack/DSAWrapperAnalysis.h"
#include "smack/LlvmCompat.h"
#include "smack/SmackOptions.h"

#include "smack/Debug.h"
#include "seadsa/InitializePasses.hh"
#include "utils/InitializePasses.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/ToolOutputFile.h"

#include <iostream>
#include <algorithm>
#include <iterator>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <tuple>

using namespace llvm;

// Pass statistics
STATISTIC(FuncAdded, "Number of bounce functions added");
STATISTIC(CSConvert, "Number of call sites converted");

const bool SKIP_INCOMPLETE_NODES = false;

static cl::opt<std::string> DevirtReportFilename(
    "smack-devirt-report",
    cl::desc("Output SMACK devirtualization target report as JSON"),
    cl::init(""), cl::value_desc("filename"));

//
// Function: getVoidPtrType()
//
// Description:
//  Return a pointer to the LLVM type for a void pointer.
//
// Return value:
//  A pointer to an LLVM type for the void pointer.
//
static inline
PointerType * getVoidPtrType (LLVMContext & C) {
  Type * Int8Type  = IntegerType::getInt8Ty(C);
  return PointerType::getUnqual(Int8Type);
}

//
// Function: castTo()
//
// Description:
//  Given an LLVM value, insert a cast instruction to make it a given type.
//
static inline Value *
castTo (Value * V, Type * Ty, std::string Name, Value * InsertPt) {
  //
  // Don't bother creating a cast if it's already the correct type.
  //
  if (V->getType() == Ty)
    return V;

  //
  // If it's a constant, just create a constant expression.
  //
  if (Constant * C = dyn_cast<Constant>(V)) {
    Constant *CE = nullptr;
    if (C->getType()->isIntegerTy() && Ty->isIntegerTy()) {
      auto srcBits = C->getType()->getIntegerBitWidth();
      auto dstBits = Ty->getIntegerBitWidth();
      CE = srcBits == dstBits ? C : ConstantExpr::getCast(
                                      srcBits < dstBits ? Instruction::ZExt
                                                        : Instruction::Trunc,
                                      C, Ty);
    } else
      CE = ConstantExpr::getBitCast(C, Ty);
    return CE;
  }

  //
  // Otherwise, insert a cast instruction.
  //
  if (auto I = dyn_cast<Instruction>(InsertPt))
    return CastInst::CreateZExtOrBitCast (V, Ty, Name, I);
  else if (auto B = dyn_cast<BasicBlock>(InsertPt))
    return CastInst::CreateZExtOrBitCast (V, Ty, Name, B);
  else
    llvm_unreachable("Unexpected insertion point.");

}

static inline bool isZExtOrBitCastable(Value* V, Type* T) {
  return CastInst::castIsValid(Instruction::ZExt, V->getType(), T) ||
         CastInst::castIsValid(Instruction::BitCast, V->getType(), T);
}

static inline bool match(CallBase *CS, const Function &F) {
  auto N = CS->arg_size();
  auto T = F.getFunctionType();
  auto M = T->getNumParams();
  auto RT = T->getReturnType();
  auto IT = CS->getType();

  if (RT != IT && !CastInst::isBitCastable(RT, IT))
    return false;

  if (N < M)
    return false;

  if (N > M && !F.isVarArg())
    return false;

  for (unsigned i=0; i<M; i++) {
    auto A = CS->getArgOperand(i);
    auto PT = T->getParamType(i);
    if (A->getType() != PT && !isZExtOrBitCastable(A, PT))
      return false;
  }

  return true;
}

static inline bool checkArgs(const CallBase *CS, const Function *F) {
  auto N = CS->arg_size();
  auto T = F->getFunctionType();
  auto M = T->getNumParams();

  if (N + 1 != M)
    return false;

  for (unsigned i=0; i<N; i++) {
    auto A = CS->getArgOperand(i);
    auto PT = T->getParamType(i+1);
    if (A->getType() != PT && !isZExtOrBitCastable(A, PT))
      return false;
  }
  return true;
}

namespace {

constexpr unsigned MaxResolveDepth = 32;

struct MemoryKey {
  const Value *base = nullptr;
  int64_t offset = 0;

  bool operator<(const MemoryKey &other) const {
    return std::tie(base, offset) < std::tie(other.base, other.offset);
  }
};

struct StoredValuesResult {
  bool complete = false;
  std::set<const Value *> values;
  std::string reason;
};

struct PointerValuesResult {
  bool complete = false;
  std::set<const Value *> values;
  std::string reason;
};

struct FunctionTargetsResult {
  bool complete = false;
  std::set<const Function *> targets;
  std::string reason;
};

struct RelativeStore {
  int64_t offset = 0;
  const Value *value = nullptr;
};

struct StoreSummaryResult {
  bool complete = false;
  std::vector<RelativeStore> stores;
  std::string reason;
};

struct TargetResolution {
  std::vector<const Function *> targets;
  bool complete = false;
  bool seaDsaComplete = false;
  bool svfComplete = false;
  bool svfDisagreement = false;
  unsigned seaDsaTargetCount = 0;
  unsigned fallbackTargetCount = 0;
  unsigned svfTargetCount = 0;
  std::string source;
  std::string reason;
  std::vector<std::string> svfTargets;
};

struct DevirtReportEntry {
  std::string callsiteId;
  unsigned callsiteIndex = 0;
  std::string function;
  std::string file;
  unsigned line = 0;
  unsigned column = 0;
  std::string instruction;
  bool seaDsaComplete = false;
  bool complete = false;
  unsigned seaDsaTargetCount = 0;
  unsigned fallbackTargetCount = 0;
  unsigned targetCount = 0;
  bool svfComplete = false;
  bool svfDisagreement = false;
  unsigned svfTargetCount = 0;
  std::string source;
  std::string reason;
  std::vector<std::string> targets;
  std::vector<std::string> svfTargets;
};

static std::vector<DevirtReportEntry> DevirtReportEntries;
static std::map<const CallBase *, unsigned> DevirtCallsiteIndices;

static bool isIgnoredTarget(const Function &F) {
  return F.getName() == "__SMACK_value";
}

static bool isNoAliasPointerResult(const Value *V) {
  if (const auto *CB = dyn_cast<CallBase>(V))
    return CB->getType()->isPointerTy() && CB->returnDoesNotAlias();
  return false;
}

static const Function *directCalledFunction(const CallBase *CB) {
  return dyn_cast<Function>(CB->getCalledOperand()->stripPointerCastsAndAliases());
}

static std::vector<const Function *>
sortedTargets(const std::set<const Function *> &targets) {
  std::vector<const Function *> out(targets.begin(), targets.end());
  std::sort(out.begin(), out.end(), [](const Function *lhs, const Function *rhs) {
    return lhs->getName() < rhs->getName();
  });
  return out;
}

static std::string valueToString(const Value &V) {
  std::string out;
  raw_string_ostream os(out);
  V.print(os);
  return os.str();
}

static unsigned indirectCallsiteIndex(const CallBase &CS) {
  const Function *F = CS.getFunction();
  unsigned index = 0;
  for (const Instruction &I : instructions(F)) {
    if (const auto *CB = dyn_cast<CallBase>(&I)) {
      if (!CB->isIndirectCall())
        continue;
      if (CB == &CS)
        return index;
      ++index;
    }
  }
  return index;
}

static std::string makeCallsiteId(const CallBase &CS, unsigned index) {
  std::string function = CS.getFunction()->getName().str();
  return function + ":indirect:" + std::to_string(index);
}

static void addDebugLoc(DevirtReportEntry &entry, const CallBase &CS) {
  if (const DebugLoc &loc = CS.getDebugLoc()) {
    entry.line = loc.getLine();
    entry.column = loc.getCol();
    if (const auto *scope = dyn_cast_or_null<DIScope>(loc.getScope()))
      entry.file = scope->getFilename().str();
  }
}

static void recordDevirtResolution(const CallBase &CS,
                                   const TargetResolution &resolution) {
  if (DevirtReportFilename.empty())
    return;

  DevirtReportEntry entry;
  auto assigned = DevirtCallsiteIndices.find(&CS);
  entry.callsiteIndex = assigned != DevirtCallsiteIndices.end()
                            ? assigned->second
                            : indirectCallsiteIndex(CS);
  entry.callsiteId = makeCallsiteId(CS, entry.callsiteIndex);
  entry.function = CS.getParent()->getParent()->getName().str();
  entry.instruction = valueToString(CS);
  entry.seaDsaComplete = resolution.seaDsaComplete;
  entry.complete = resolution.complete;
  entry.seaDsaTargetCount = resolution.seaDsaTargetCount;
  entry.fallbackTargetCount = resolution.fallbackTargetCount;
  entry.targetCount = resolution.targets.size();
  entry.svfComplete = resolution.svfComplete;
  entry.svfDisagreement = resolution.svfDisagreement;
  entry.svfTargetCount = resolution.svfTargetCount;
  entry.source = resolution.source;
  entry.reason = resolution.reason;
  addDebugLoc(entry, CS);
  for (const Function *F : resolution.targets)
    entry.targets.push_back(F->getName().str());
  entry.svfTargets = resolution.svfTargets;
  DevirtReportEntries.push_back(std::move(entry));
}

static void writeDevirtReport(const Module &M) {
  if (DevirtReportFilename.empty())
    return;

  std::error_code EC;
  ToolOutputFile F(DevirtReportFilename.c_str(), EC, sys::fs::OF_Text);
  if (EC) {
    errs() << "Could not write " << DevirtReportFilename << ": "
           << EC.message() << "\n";
    return;
  }

  json::OStream J(F.os(), 2);
  J.object([&] {
    J.attribute("schema_version", 2);
    J.attribute("module", M.getModuleIdentifier());
    J.attributeArray("callsites", [&] {
      for (const auto &entry : DevirtReportEntries) {
        J.object([&] {
          J.attribute("callsite_id", entry.callsiteId);
          J.attribute("callsite_index", entry.callsiteIndex);
          J.attribute("function", entry.function);
          if (entry.file.empty())
            J.attribute("file", json::Value(nullptr));
          else
            J.attribute("file", entry.file);
          J.attribute("line", entry.line);
          J.attribute("column", entry.column);
          J.attribute("instruction", entry.instruction);
          J.attribute("sea_dsa_complete", entry.seaDsaComplete);
          J.attribute("complete", entry.complete);
          J.attribute("sea_dsa_target_count", entry.seaDsaTargetCount);
          J.attribute("fallback_target_count", entry.fallbackTargetCount);
          J.attribute("target_count", entry.targetCount);
          J.attribute("svf_complete", entry.svfComplete);
          J.attribute("svf_disagreement", entry.svfDisagreement);
          J.attribute("svf_target_count", entry.svfTargetCount);
          J.attribute("source", entry.source);
          J.attribute("reason", entry.reason);
          J.attributeArray("targets", [&] {
            for (const auto &target : entry.targets)
              J.value(target);
          });
          J.attributeArray("svf_targets", [&] {
            for (const auto &target : entry.svfTargets)
              J.value(target);
          });
        });
      }
    });
  });
  F.keep();
}

class DevirtTargetResolver {
  CallBase *CS;
  Module &M;
  const DataLayout &DL;
  seadsa::CompleteCallGraph *CCG;
  const smack::MemoryPartitionOracle *Oracle;

  std::set<const Value *> resolvingFunctionValues;
  std::set<const Value *> resolvingPointerValues;
  std::set<MemoryKey> resolvingMemory;
  std::set<std::pair<const Function *, unsigned>> resolvingSummaries;

public:
  DevirtTargetResolver(CallBase *CS, seadsa::CompleteCallGraph *CCG,
                       const DataLayout &DL,
                       const smack::MemoryPartitionOracle *Oracle)
      : CS(CS), M(*CS->getParent()->getParent()->getParent()), DL(DL),
        CCG(CCG), Oracle(Oracle) {}

  TargetResolution resolve() {
    TargetResolution result;
    std::vector<const Function *> fallbackTargets = broadFallbackTargets();
    result.fallbackTargetCount = fallbackTargets.size();
    FunctionTargetsResult svfTargets = resolveSVFTargets();

    std::set<const Function *> seaTargets;
    if (CCG && CCG->isComplete(*CS)) {
      result.seaDsaComplete = true;
      for (auto F = CCG->begin(*CS); F != CCG->end(*CS); ++F)
        addCallableTarget(*F, seaTargets);
      result.seaDsaTargetCount = seaTargets.size();
    }

    FunctionTargetsResult precise =
        resolveFunctionTargets(CS->getCalledOperand(), 0);

    if (result.seaDsaComplete) {
      if (precise.complete && !precise.targets.empty()) {
        if (seaTargets == precise.targets) {
          result.targets = sortedTargets(seaTargets);
          result.complete = true;
          result.source = "sea-dsa";
          result.reason = "sea-dsa-validated";
          return applySVFTargets(std::move(result), svfTargets);
        }

        std::set<const Function *> mergedTargets = seaTargets;
        mergedTargets.insert(precise.targets.begin(), precise.targets.end());
        result.targets = sortedTargets(mergedTargets);
        result.complete = false;
        result.source = "hybrid";
        result.reason = "sea-dsa-type-dataflow-disagreement";
        return applySVFTargets(std::move(result), svfTargets);
      }

      result.targets = std::move(fallbackTargets);
      result.complete = false;
      result.source = "fallback";
      result.reason = precise.reason.empty() ? "sea-dsa-unvalidated"
                                             : "sea-dsa-unvalidated-" + precise.reason;
      return applySVFTargets(std::move(result), svfTargets);
    }

    if (precise.complete && !precise.targets.empty()) {
      result.targets = sortedTargets(precise.targets);
      result.complete = true;
      result.source = "type-dataflow";
      result.reason = precise.reason;
      return applySVFTargets(std::move(result), svfTargets);
    }

    result.targets = std::move(fallbackTargets);
    result.complete = false;
    result.source = "fallback";
    result.reason =
        precise.reason.empty() ? "incomplete-target-flow" : precise.reason;
    return applySVFTargets(std::move(result), svfTargets);
  }

private:
  static std::set<const Function *>
  targetSetFromVector(const std::vector<const Function *> &targets) {
    return {targets.begin(), targets.end()};
  }

  static std::vector<std::string>
  targetNames(const std::set<const Function *> &targets) {
    std::vector<std::string> names;
    for (const Function *F : sortedTargets(targets))
      names.push_back(F->getName().str());
    return names;
  }

  TargetResolution applySVFTargets(TargetResolution result,
                                   const FunctionTargetsResult &svf) {
    if (svf.complete) {
      result.svfComplete = true;
      result.svfTargetCount = svf.targets.size();
      result.svfTargets = targetNames(svf.targets);
    }

    if (!svf.complete || svf.targets.empty())
      return result;

    if (!result.complete) {
      result.targets = sortedTargets(svf.targets);
      result.complete = true;
      result.source = "svf";
      result.reason = "svf-complete";
      return result;
    }

    std::set<const Function *> current = targetSetFromVector(result.targets);
    if (current == svf.targets)
      return result;

    current.insert(svf.targets.begin(), svf.targets.end());
    result.targets = sortedTargets(current);
    result.complete = false;
    result.svfDisagreement = true;
    result.source = "hybrid-svf";
    result.reason += "-svf-disagreement";
    return result;
  }

  FunctionTargetsResult resolveSVFTargets() {
    if (!Oracle)
      return incompleteFunctionTargets("svf-oracle-missing");

    const auto *targets = Oracle->lookupIndirectCallTargets(
        smack::MemoryPartitionOracle::instructionKey(*CS));
    if (!targets)
      return incompleteFunctionTargets("svf-targets-missing");
    if (!targets->complete)
      return incompleteFunctionTargets("svf-targets-incomplete");

    std::set<const Function *> resolved;
    for (const std::string &targetName : targets->targets) {
      Function *F = M.getFunction(targetName);
      if (!F)
        return incompleteFunctionTargets("svf-target-missing");
      unsigned before = resolved.size();
      addCallableTarget(F, resolved);
      if (resolved.size() == before)
        return incompleteFunctionTargets("svf-target-incompatible");
    }
    return completeFunctionTargets(std::move(resolved), "svf-targets");
  }

  void addCallableTarget(const Function *F, std::set<const Function *> &targets) {
    if (!F || isIgnoredTarget(*F))
      return;
    if (match(CS, *F))
      targets.insert(F);
  }

  std::vector<const Function *> broadFallbackTargets() {
    std::set<const Function *> targets;
    for (auto &F : M) {
      if (F.hasAddressTaken())
        addCallableTarget(&F, targets);
    }
    return sortedTargets(targets);
  }

  FunctionTargetsResult completeFunctionTargets(std::set<const Function *> targets,
                                                std::string reason) {
    return {true, std::move(targets), std::move(reason)};
  }

  FunctionTargetsResult incompleteFunctionTargets(std::string reason) {
    return {false, {}, std::move(reason)};
  }

  PointerValuesResult completePointers(std::set<const Value *> values,
                                       std::string reason) {
    return {true, std::move(values), std::move(reason)};
  }

  PointerValuesResult incompletePointers(std::string reason) {
    return {false, {}, std::move(reason)};
  }

  StoredValuesResult completeStored(std::set<const Value *> values,
                                    std::string reason) {
    return {true, std::move(values), std::move(reason)};
  }

  StoredValuesResult incompleteStored(std::string reason) {
    return {false, {}, std::move(reason)};
  }

  FunctionTargetsResult
  unionFunctionResults(const std::vector<FunctionTargetsResult> &results,
                       std::string reason) {
    std::set<const Function *> targets;
    for (const auto &result : results) {
      if (!result.complete)
        return incompleteFunctionTargets(result.reason);
      targets.insert(result.targets.begin(), result.targets.end());
    }
    return completeFunctionTargets(std::move(targets), std::move(reason));
  }

  PointerValuesResult
  unionPointerResults(const std::vector<PointerValuesResult> &results,
                      std::string reason) {
    std::set<const Value *> values;
    for (const auto &result : results) {
      if (!result.complete)
        return incompletePointers(result.reason);
      values.insert(result.values.begin(), result.values.end());
    }
    return completePointers(std::move(values), std::move(reason));
  }

  FunctionTargetsResult resolveFunctionTargets(const Value *V, unsigned depth) {
    if (!V)
      return incompleteFunctionTargets("null-callee-value");
    if (depth > MaxResolveDepth)
      return incompleteFunctionTargets("target-depth-limit");

    V = V->stripPointerCastsAndAliases();
    if (!resolvingFunctionValues.insert(V).second)
      return incompleteFunctionTargets("recursive-target-flow");

    auto done = [&](FunctionTargetsResult result) {
      resolvingFunctionValues.erase(V);
      return result;
    };

    if (const auto *F = dyn_cast<Function>(V)) {
      std::set<const Function *> targets;
      addCallableTarget(F, targets);
      return done(completeFunctionTargets(std::move(targets), "constant-function"));
    }

    if (isa<ConstantPointerNull>(V))
      return done(completeFunctionTargets({}, "null-function-pointer"));

    if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
      if (CE->isCast())
        return done(resolveFunctionTargets(CE->getOperand(0), depth + 1));
      return done(incompleteFunctionTargets("constant-expression-not-function"));
    }

    if (const auto *BC = dyn_cast<BitCastOperator>(V))
      return done(resolveFunctionTargets(BC->getOperand(0), depth + 1));

    if (const auto *PN = dyn_cast<PHINode>(V)) {
      std::vector<FunctionTargetsResult> incoming;
      for (const Value *IV : PN->incoming_values())
        incoming.push_back(resolveFunctionTargets(IV, depth + 1));
      return done(unionFunctionResults(incoming, "phi-union"));
    }

    if (const auto *SI = dyn_cast<SelectInst>(V)) {
      std::vector<FunctionTargetsResult> arms;
      arms.push_back(resolveFunctionTargets(SI->getTrueValue(), depth + 1));
      arms.push_back(resolveFunctionTargets(SI->getFalseValue(), depth + 1));
      return done(unionFunctionResults(arms, "select-union"));
    }

    if (const auto *LI = dyn_cast<LoadInst>(V)) {
      StoredValuesResult stored = storedValuesForLoad(LI, depth + 1);
      if (!stored.complete)
        return done(incompleteFunctionTargets(stored.reason));
      std::vector<FunctionTargetsResult> resolved;
      for (const Value *SV : stored.values)
        resolved.push_back(resolveFunctionTargets(SV, depth + 1));
      return done(unionFunctionResults(resolved, stored.reason));
    }

    if (const auto *CB = dyn_cast<CallBase>(V))
      return done(resolveReturnFunctionTargets(CB, depth + 1));

    return done(incompleteFunctionTargets("unsupported-target-value"));
  }

  PointerValuesResult resolvePointerValues(const Value *V, unsigned depth) {
    if (!V || !V->getType()->isPointerTy())
      return incompletePointers("not-a-pointer-value");
    if (depth > MaxResolveDepth)
      return incompletePointers("pointer-depth-limit");

    V = V->stripPointerCastsAndAliases();
    if (!resolvingPointerValues.insert(V).second)
      return incompletePointers("recursive-pointer-flow");

    auto done = [&](PointerValuesResult result) {
      resolvingPointerValues.erase(V);
      return result;
    };

    if (isa<ConstantPointerNull>(V))
      return done(completePointers({}, "null-pointer"));

    if (isa<GlobalValue>(V) || isa<AllocaInst>(V) || isa<GetElementPtrInst>(V) ||
        isa<Argument>(V) || isNoAliasPointerResult(V))
      return done(completePointers({V}, "pointer-base"));

    if (const auto *CE = dyn_cast<ConstantExpr>(V)) {
      if (CE->isCast())
        return done(resolvePointerValues(CE->getOperand(0), depth + 1));
      if (CE->getOpcode() == Instruction::GetElementPtr)
        return done(completePointers({V}, "constant-gep"));
      return done(incompletePointers("unsupported-constant-pointer"));
    }

    if (const auto *BC = dyn_cast<BitCastOperator>(V))
      return done(resolvePointerValues(BC->getOperand(0), depth + 1));

    if (const auto *PN = dyn_cast<PHINode>(V)) {
      std::vector<PointerValuesResult> incoming;
      for (const Value *IV : PN->incoming_values())
        incoming.push_back(resolvePointerValues(IV, depth + 1));
      return done(unionPointerResults(incoming, "pointer-phi-union"));
    }

    if (const auto *SI = dyn_cast<SelectInst>(V)) {
      std::vector<PointerValuesResult> arms;
      arms.push_back(resolvePointerValues(SI->getTrueValue(), depth + 1));
      arms.push_back(resolvePointerValues(SI->getFalseValue(), depth + 1));
      return done(unionPointerResults(arms, "pointer-select-union"));
    }

    if (const auto *LI = dyn_cast<LoadInst>(V)) {
      StoredValuesResult stored = storedValuesForLoad(LI, depth + 1);
      if (!stored.complete)
        return done(incompletePointers(stored.reason));
      std::vector<PointerValuesResult> resolved;
      for (const Value *SV : stored.values)
        resolved.push_back(resolvePointerValues(SV, depth + 1));
      return done(unionPointerResults(resolved, stored.reason));
    }

    if (const auto *CB = dyn_cast<CallBase>(V))
      return done(resolveReturnPointers(CB, depth + 1));

    return done(incompletePointers("unsupported-pointer-value"));
  }

  FunctionTargetsResult resolveReturnFunctionTargets(const CallBase *CB,
                                                     unsigned depth) {
    const Function *callee = directCalledFunction(CB);
    if (!callee || callee->isDeclaration())
      return incompleteFunctionTargets("unknown-return-function");

    std::vector<FunctionTargetsResult> returns;
    for (const BasicBlock &BB : *callee) {
      if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
        if (!RI->getReturnValue())
          continue;
        returns.push_back(resolveFunctionTargets(RI->getReturnValue(), depth + 1));
      }
    }
    if (returns.empty())
      return incompleteFunctionTargets("function-pointer-return-without-value");
    return unionFunctionResults(returns, "return-function-union");
  }

  PointerValuesResult resolveReturnPointers(const CallBase *CB, unsigned depth) {
    if (CB->getType()->isPointerTy() && CB->returnDoesNotAlias())
      return completePointers({CB}, "noalias-call-result");

    const Function *callee = directCalledFunction(CB);
    if (!callee || callee->isDeclaration())
      return incompletePointers("unknown-return-pointer");

    std::vector<PointerValuesResult> returns;
    for (const BasicBlock &BB : *callee) {
      if (const auto *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
        if (!RI->getReturnValue())
          continue;
        returns.push_back(resolvePointerValues(RI->getReturnValue(), depth + 1));
      }
    }
    if (returns.empty())
      return incompletePointers("pointer-return-without-value");
    return unionPointerResults(returns, "return-pointer-union");
  }

  StoredValuesResult storedValuesForLoad(const LoadInst *LI, unsigned depth) {
    auto keys = memoryKeysForPointer(LI->getPointerOperand(), depth + 1);
    if (!keys.complete)
      return incompleteStored(keys.reason);

    std::set<const Value *> values;
    for (const MemoryKey &key : keys.keys) {
      StoredValuesResult stored =
          storedValuesForKey(key, LI->getFunction(), depth + 1);
      if (!stored.complete)
        return incompleteStored(stored.reason);
      values.insert(stored.values.begin(), stored.values.end());
    }
    return completeStored(std::move(values), keys.reason);
  }

  struct MemoryKeysResult {
    bool complete = false;
    std::set<MemoryKey> keys;
    std::string reason;
  };

  MemoryKeysResult memoryKeysForPointer(const Value *Ptr, unsigned depth) {
    if (!Ptr || !Ptr->getType()->isPointerTy())
      return {false, {}, "memory-pointer-not-pointer"};
    if (depth > MaxResolveDepth)
      return {false, {}, "memory-key-depth-limit"};

    int64_t offset = 0;
    const Value *base = GetPointerBaseWithConstantOffset(Ptr, offset, DL);
    PointerValuesResult bases = resolvePointerValues(base, depth + 1);
    if (!bases.complete)
      return {false, {}, bases.reason};

    std::set<MemoryKey> keys;
    for (const Value *baseValue : bases.values) {
      if (!baseValue || !baseValue->getType()->isPointerTy())
        continue;
      int64_t baseOffset = 0;
      const Value *baseBase =
          GetPointerBaseWithConstantOffset(baseValue, baseOffset, DL);
      keys.insert({baseBase, offset + baseOffset});
    }

    if (keys.empty())
      return {false, {}, "empty-memory-key-set"};
    return {true, std::move(keys), "memory-key"};
  }

  StoredValuesResult storedValuesForKey(const MemoryKey &key,
                                        const Function *context,
                                        unsigned depth) {
    if (!key.base || !context)
      return incompleteStored("missing-memory-context");
    if (depth > MaxResolveDepth)
      return incompleteStored("stored-value-depth-limit");
    if (!resolvingMemory.insert(key).second)
      return incompleteStored("recursive-memory-flow");

    auto done = [&](StoredValuesResult result) {
      resolvingMemory.erase(key);
      return result;
    };

    std::set<const Value *> values;
    bool sawWriter = false;

    if (const auto *GV = dyn_cast<GlobalVariable>(key.base)) {
      if (GV->hasInitializer()) {
        if (const Constant *C =
                constantAtOffset(GV->getInitializer(), key.offset)) {
          values.insert(C);
          sawWriter = true;
        }
      }
      if (GV->isConstant())
        return sawWriter
                   ? done(completeStored(std::move(values), "constant-global"))
                   : done(incompleteStored("constant-global-offset-miss"));
    }

    const bool scanWholeModule = isa<GlobalVariable>(key.base);
    for (const Function &F : M) {
      if (F.isDeclaration())
        continue;
      if (!scanWholeModule && &F != context)
        continue;

      for (const Instruction &I : instructions(F)) {
        if (const auto *SI = dyn_cast<StoreInst>(&I)) {
          auto storeKeys = memoryKeysForPointer(SI->getPointerOperand(), depth + 1);
          if (storeKeys.complete && storeKeys.keys.count(key)) {
            values.insert(SI->getValueOperand());
            sawWriter = true;
          }

          PointerValuesResult storedPtrs =
              resolvePointerValues(SI->getValueOperand(), depth + 1);
          if (storedPtrs.complete && storedPtrs.values.count(key.base)) {
            bool storedOnlyInLocalSlot = false;
            if (storeKeys.complete) {
              storedOnlyInLocalSlot = !storeKeys.keys.empty();
              for (const MemoryKey &storeKey : storeKeys.keys)
                storedOnlyInLocalSlot =
                    storedOnlyInLocalSlot && isa<AllocaInst>(storeKey.base);
            }
            if (!storedOnlyInLocalSlot)
              return done(incompleteStored("memory-base-escapes-through-store"));
          }
        }

        if (const auto *CB = dyn_cast<CallBase>(&I)) {
          if (CB == CS)
            continue;
          if (!callMayTouchKey(CB, key, values, sawWriter, depth + 1))
            return done(incompleteStored("memory-base-escapes-through-call"));
        }
      }
    }

    if (!sawWriter)
      return done(incompleteStored("no-known-store"));
    return done(completeStored(std::move(values), "known-stores"));
  }

  bool callMayTouchKey(const CallBase *CB, const MemoryKey &key,
                       std::set<const Value *> &values, bool &sawWriter,
                       unsigned depth) {
    const Function *callee = directCalledFunction(CB);

    for (unsigned i = 0; i < CB->arg_size(); ++i) {
      const Value *arg = CB->getArgOperand(i);
      if (!arg->getType()->isPointerTy())
        continue;

      auto argKeys = memoryKeysForPointer(arg, depth + 1);
      if (!argKeys.complete)
        continue;

      for (const MemoryKey &argKey : argKeys.keys) {
        if (argKey.base != key.base)
          continue;

        if (!callee || callee->isDeclaration())
          return false;

        StoreSummaryResult summary = summarizeStoresToArgument(callee, i, depth + 1);
        if (!summary.complete)
          return false;

        for (const RelativeStore &store : summary.stores) {
          if (argKey.offset + store.offset == key.offset) {
            values.insert(store.value);
            sawWriter = true;
          }
        }
      }
    }

    return true;
  }

  StoreSummaryResult summarizeStoresToArgument(const Function *F, unsigned argNo,
                                               unsigned depth) {
    if (!F || F->isDeclaration() || argNo >= F->arg_size())
      return {false, {}, "missing-store-summary"};
    if (depth > MaxResolveDepth)
      return {false, {}, "store-summary-depth-limit"};

    auto cacheKey = std::make_pair(F, argNo);
    if (!resolvingSummaries.insert(cacheKey).second)
      return {true, {}, "recursive-store-summary"};

    auto done = [&](StoreSummaryResult result) {
      resolvingSummaries.erase(cacheKey);
      return result;
    };

    const Argument *arg = F->getArg(argNo);
    std::vector<RelativeStore> stores;

    for (const Instruction &I : instructions(F)) {
      if (const auto *SI = dyn_cast<StoreInst>(&I)) {
        auto rel = relativeKeyToArgument(SI->getPointerOperand(), arg, depth + 1);
        if (rel)
          stores.push_back({*rel, SI->getValueOperand()});
      }

      if (const auto *CB = dyn_cast<CallBase>(&I)) {
        const Function *callee = directCalledFunction(CB);
        if (!callee || callee->isDeclaration()) {
          if (argumentEscapesToCall(CB, arg, depth + 1))
            return done({false, {}, "argument-escapes-to-unknown-call"});
          continue;
        }

        for (unsigned i = 0; i < CB->arg_size(); ++i) {
          const Value *actual = CB->getArgOperand(i);
          if (!actual->getType()->isPointerTy())
            continue;
          auto rel = relativeKeyToArgument(actual, arg, depth + 1);
          if (!rel)
            continue;

          StoreSummaryResult nested =
              summarizeStoresToArgument(callee, i, depth + 1);
          if (!nested.complete)
            return done(nested);
          for (const RelativeStore &nestedStore : nested.stores)
            stores.push_back({*rel + nestedStore.offset, nestedStore.value});
        }
      }
    }

    return done({true, std::move(stores), "argument-store-summary"});
  }

  std::optional<int64_t> relativeKeyToArgument(const Value *Ptr,
                                               const Argument *arg,
                                               unsigned depth) {
    auto keys = memoryKeysForPointer(Ptr, depth + 1);
    if (!keys.complete)
      return std::nullopt;
    if (keys.keys.size() != 1)
      return std::nullopt;
    const MemoryKey &key = *keys.keys.begin();
    if (key.base != arg)
      return std::nullopt;
    return key.offset;
  }

  bool argumentEscapesToCall(const CallBase *CB, const Argument *arg,
                             unsigned depth) {
    for (unsigned i = 0; i < CB->arg_size(); ++i) {
      const Value *actual = CB->getArgOperand(i);
      if (!actual->getType()->isPointerTy())
        continue;
      auto rel = relativeKeyToArgument(actual, arg, depth + 1);
      if (rel)
        return true;
    }
    return false;
  }

  const Constant *constantAtOffset(const Constant *C, int64_t offset) {
    if (!C || offset < 0)
      return nullptr;

    if (offset == 0 && C->getType()->isPointerTy())
      return C;

    if (const auto *CE = dyn_cast<ConstantExpr>(C)) {
      if (offset == 0 && CE->getType()->isPointerTy())
        return CE;
      return nullptr;
    }

    if (const auto *ST = dyn_cast<StructType>(C->getType())) {
      if (!ST->isSized())
        return nullptr;
      const StructLayout *layout =
          DL.getStructLayout(const_cast<StructType *>(ST));
      for (unsigned i = 0; i < ST->getNumElements(); ++i) {
        uint64_t elemOffset = layout->getElementOffset(i);
        Type *elemTy = ST->getElementType(i);
        uint64_t elemSize = smack::fixedTypeAllocSize(DL, elemTy);
        if (static_cast<uint64_t>(offset) < elemOffset ||
            static_cast<uint64_t>(offset) >= elemOffset + elemSize)
          continue;
        if (const Constant *elem = C->getAggregateElement(i))
          return constantAtOffset(elem, offset - elemOffset);
        return nullptr;
      }
      return nullptr;
    }

    if (const auto *AT = dyn_cast<ArrayType>(C->getType())) {
      Type *elemTy = AT->getElementType();
      if (!elemTy->isSized())
        return nullptr;
      uint64_t elemSize = smack::fixedTypeAllocSize(DL, elemTy);
      if (!elemSize)
        return nullptr;
      uint64_t index = static_cast<uint64_t>(offset) / elemSize;
      uint64_t rem = static_cast<uint64_t>(offset) % elemSize;
      if (index >= AT->getNumElements())
        return nullptr;
      if (const Constant *elem = C->getAggregateElement(index))
        return constantAtOffset(elem, rem);
      return nullptr;
    }

    if (offset == 0 && isa<ConstantAggregateZero>(C))
      return nullptr;

    return nullptr;
  }
};

} // namespace

//
// Method: findInCache()
//
// Description:
//  This method looks through the cache of bounce functions to see if there
//  exists a bounce function for the specified call site.
//
// Return value:
//  0 - No usable bounce function has been created.
//  Otherwise, a pointer to a bounce that can replace the call site is
//  returned.
//
const Function *
Devirtualize::findInCache (const CallBase *CS,
                           std::set<const Function*>& Targets) {
  //
  // Iterate through all of the existing bounce functions to see if one of them
  // can be resued.
  //
  std::map<const Function *, std::set<const Function *> >::iterator I;
  for (I = bounceCache.begin(); I != bounceCache.end(); ++I) {
    //
    // If the bounce function and the function pointer have different types,
    // then skip this bounce function because it is incompatible.
    //
    const Function * bounceFunc = I->first;

    // Check the return type
    if (CS->getType() != bounceFunc->getReturnType())
      continue;

    // Check the type of the function pointer and the argumentsa
    PointerType* PT = dyn_cast<PointerType>(bounceFunc->arg_begin()->getType());
    assert(PT);
    if (CS->getCalledOperand()->stripPointerCastsAndAliases()->getType() != PT)
      continue;

    FunctionType* FT = CS->getFunctionType();
    if (FT->isVarArg() && !checkArgs(CS, bounceFunc))
      continue;

    //
    // Determine whether the targets are identical.  If so, then this function
    // can be used as a bounce function for this call site.
    //
    if (Targets == I->second)
      return I->first;
  }

  //
  // No suiteable bounce function was found.
  //
  return 0;
}

//
// Method: buildBounce()
//
// Description:
//  Replaces the given call site with a call to a bounce function.  The
//  bounce function compares the function pointer to one of the given
//  target functions and calls the function directly if the pointer
//  matches.
//
Function*
Devirtualize::buildBounce (CallBase *CS, std::vector<const Function*>& Targets) {
  //
  // Update the statistics on the number of bounce functions added to the
  // module.
  //
  ++FuncAdded;
  //
  // Create a bounce function that has a function signature almost identical
  // to the function being called.  The only difference is that it will have
  // an additional pointer argument at the beginning of its argument list that
  // will be the function to call.
  //
  Value* ptr = CS->getCalledOperand();
  std::vector<Type *> TP;
  TP.insert (TP.begin(), ptr->getType());
  for (auto i = CS->arg_begin();
       i != CS->arg_end();
       ++i) {
    TP.push_back ((*i)->getType());
  }

  FunctionType* NewTy = FunctionType::get(CS->getType(), TP, false);
  Module * M = CS->getParent()->getParent()->getParent();
  Function* F = Function::Create (NewTy,
                                  GlobalValue::InternalLinkage,
                                  "devirtbounce",
                                  M);

  //
  // Set the names of the arguments.
  //
  F->arg_begin()->setName("funcPtr");
  for (auto A = std::next(F->arg_begin()), E = F->arg_end(); A != E; ++A)
    A->setName("arg");

  //
  // Create an entry basic block for the function.  All it should do is perform
  // some cast instructions and branch to the first comparison basic block.
  //
  BasicBlock* entryBB = BasicBlock::Create (M->getContext(), "entry", F);

  //
  // For each function target, create a basic block that will call that
  // function directly.
  //
  std::map<const Function*, BasicBlock*> targets;
  for (unsigned index = 0; index < Targets.size(); ++index) {
    const Function* FL = Targets[index];
    const FunctionType* FT = FL->getFunctionType();

    // Create the basic block for doing the direct call
    BasicBlock* BL = BasicBlock::Create (M->getContext(), FL->getName(), F);
    targets[FL] = BL;
    // Create the direct function call

    std::vector<Value*> Args;
    Function::arg_iterator P, PE;
    FunctionType::param_iterator T, TE;
    for (P = std::next(F->arg_begin()), PE = F->arg_end(),
         T = FT->param_begin(), TE = FT->param_end();
         P != PE && T != TE; ++P, ++T)
      Args.push_back(castTo(&*P, *T, "", BL));

    Value* directCall = CallInst::Create (const_cast<Function*>(FL),
                                          Args,
                                          "",
                                          BL);

    // Add the return instruction for the basic block
    if (CS->getType()->isVoidTy())
      ReturnInst::Create (M->getContext(), BL);
    else
      ReturnInst::Create (M->getContext(), directCall, BL);
  }

  //
  // Create a failure basic block.  This basic block should simply be an
  // unreachable instruction.
  //
  BasicBlock * failBB = BasicBlock::Create (M->getContext(),
                                            "fail",
                                            F);

  // TODO what to do when there are no potential targets?
  if (Targets.size())
    new UnreachableInst (M->getContext(), failBB);
  else
    ReturnInst::Create(M->getContext(), failBB);

  //
  // Setup the entry basic block.  For now, just have it call the failure
  // basic block.  We'll change the basic block to which it branches later.
  //
  BranchInst * InsertPt = BranchInst::Create (failBB, entryBB);

  //
  // Create basic blocks which will test the value of the incoming function
  // pointer and branch to the appropriate basic block to call the function.
  //
  Type * VoidPtrType = getVoidPtrType (M->getContext());
  Value * FArg = castTo (&*F->arg_begin(), VoidPtrType, "", InsertPt);
  BasicBlock * tailBB = failBB;
  for (unsigned index = 0; index < Targets.size(); ++index) {
    //
    // Cast the function pointer to an integer.  This can go in the entry
    // block.
    //
    Value * TargetInt = castTo (const_cast<Function*>(Targets[index]),
                                VoidPtrType,
                                "",
                                InsertPt);

    //
    // Create a new basic block that compares the function pointer to the
    // function target.  If the function pointer matches, we'll branch to the
    // basic block performing the direct call for that function; otherwise,
    // we'll branch to the next function call target.
    //
    BasicBlock* TB = targets[Targets[index]];
    BasicBlock* newB = BasicBlock::Create (M->getContext(),
                                           "test." + Targets[index]->getName(),
                                           F);
    CmpInst * setcc = CmpInst::Create (Instruction::ICmp,
                                       CmpInst::ICMP_EQ,
                                       TargetInt,
                                       FArg,
                                       "sc",
                                       newB);
    BranchInst::Create (TB, tailBB, setcc, newB);

    //
    // Make this newly created basic block the next block that will be reached
    // when the next comparison will need to be done.
    //
    tailBB = newB;
  }

  //
  // Make the entry basic block branch to the first comparison basic block.
  //
  InsertPt->setSuccessor(0, tailBB);
  //
  // Return the newly created bounce function.
  //
  return F;
}

//
// Method: makeDirectCall()
//
// Description:
//  Transform the specified call site into a direct call.
//
// Inputs:
//  CS - The call site to transform.
//
// Preconditions:
//  1) This method assumes that CS is an indirect call site.
//  2) This method assumes that a pointer to the CallTarget analysis pass has
//     already been acquired by the class.
//
void
Devirtualize::makeDirectCall (CallBase *CS) {
  //
  // Find the targets of the indirect function call.
  //

  DevirtTargetResolver resolver(CS, CCG, *TD, Oracle.get());
  TargetResolution resolution = resolver.resolve();
  std::vector<const Function*> Targets = resolution.targets;
  recordDevirtResolution(*CS, resolution);

  if (Targets.empty())
    return;

  //
  // Determine if an existing bounce function can be used for this call site.
  //
  std::set<const Function *> targetSet (Targets.begin(), Targets.end());
  const Function * NF = findInCache (CS, targetSet);

  //
  // If no cached bounce function was found, build a function which will
  // implement a switch statement.  The switch statement will determine which
  // function target to call and call it.
  //
  if (!NF) {
    // Build the bounce function and add it to the cache
    NF = buildBounce (CS, Targets);
    bounceCache[NF] = targetSet;
  }

  //
  // Replace the original call with a call to the bounce function.
  //
  if (CallInst* CI = dyn_cast<CallInst>(CS)) {
    std::vector<Value*> Params;
    Params.push_back(CI->getCalledOperand());
    for (unsigned i=0; i<CI->arg_size(); i++) {
      Params.push_back(
        castTo(CI->getArgOperand(i), NF->getFunctionType()->getParamType(i+1), "", CS)
      );
    }

    std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
    CallInst* CN = CallInst::Create (const_cast<Function*>(NF),
                                       Params,
                                       name,
                                       CI);
    CI->replaceAllUsesWith(CN);
    CI->eraseFromParent();
  } else if (InvokeInst* CI = dyn_cast<InvokeInst>(CS)) {
    std::vector<Value*> Params;
    Params.push_back(CI->getCalledOperand());
    for (unsigned i=0; i<CI->arg_size(); i++)
      Params.push_back(
        castTo(CI->getArgOperand(i), NF->getFunctionType()->getParamType(i+1), "", CS)
      );
    std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
    InvokeInst* CN = InvokeInst::Create(const_cast<Function*>(NF),
                                        CI->getNormalDest(),
                                        CI->getUnwindDest(),
                                        Params,
                                        name,
                                        CI);
    CI->replaceAllUsesWith(CN);
    CI->eraseFromParent();
  }

  //
  // Update the statistics on the number of transformed call sites.
  //
  ++CSConvert;

  return;
}

//
// Method: processCallSite()
//
// Description:
//  Examine the specified call site.  If it is an indirect call, mark it for
//  transformation into a direct call.
//
void
Devirtualize::processCallSite (CallBase *CS) {
  //
  // First, determine if this is a direct call.  If so, then just ignore it.
  //
  if (!CS->isIndirectCall())
    return;

  //
  // Second, we will only transform those call sites which are complete (i.e.,
  // for which we know all of the call targets).
  //
  if (SKIP_INCOMPLETE_NODES && !CCG->isComplete(*CS))
    return;

  //
  // This is an indirect call site.  Put it in the worklist of call sites to
  // transforms.
  //
  DevirtCallsiteIndices[CS] = Worklist.size();
  Worklist.push_back(CS);
  return;
}

//
// Method: runOnModule()
//
// Description:
//  Entry point for this LLVM transform pass.  Look for indirect function calls
//  and turn them into direct function calls.
//
bool
Devirtualize::runOnModule (Module & M) {
  Worklist.clear();
  DevirtCallsiteIndices.clear();
  if (!DevirtReportFilename.empty())
    DevirtReportEntries.clear();

  //
  // Get the targets of indirect function calls.
  //
  if (!CCG)
    CCG = &getAnalysis<seadsa::CompleteCallGraph>();

  //
  // Get information on the target system.
  //
  //
  TD = &M.getDataLayout();

  Oracle.reset();
  const bool useSVFIndirectTargets =
      (smack::SmackOptions::SVFIndirectCalls ||
       smack::SmackOptions::MemoryPartitioner.getValue() == "svf-refined" ||
       smack::SmackOptions::MemoryPartitioner.getValue() == "svf-native") &&
      !smack::SmackOptions::NoMemoryRegionSplitting &&
      !smack::SmackOptions::MemoryPartitionOracle.getValue().empty();
  if (useSVFIndirectTargets)
    Oracle = smack::MemoryPartitionOracle::loadFromFile(
        smack::SmackOptions::MemoryPartitionOracle.getValue(), M);

  // Visit all of the call instructions in this function and record those that
  // are indirect function calls.
  //
  visit (M);

  //
  // Now go through and transform all of the indirect calls that we found that
  // need transforming.
  //
  for (unsigned index = 0; index < Worklist.size(); ++index) {
    // Autobots, transform (the call site)!
    makeDirectCall (Worklist[index]);
  }

  writeDevirtReport(M);

  //
  // Conservatively assume that we've changed one or more call sites.
  //
  return true;
}

// Pass ID variable
char Devirtualize::ID = 0;

llvm::PreservedAnalyses
DevirtualizeNewPM::run(Module &M, ModuleAnalysisManager &MAM) {
  auto &ccgResult = MAM.getResult<smack::CompleteCallGraphAnalysis>(M);
  Devirtualize pass;
  pass.setCCG(static_cast<seadsa::CompleteCallGraph *>(ccgResult.ccg));
  bool changed = pass.runOnModule(M);
  return changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

using namespace seadsa;
// Pass registration
INITIALIZE_PASS_BEGIN(Devirtualize, "devirt", "Devirtualize indirect function calls", false, false)
INITIALIZE_PASS_DEPENDENCY(CompleteCallGraph)
INITIALIZE_PASS_END(Devirtualize, "devirt", "Devirtualize indirect function calls", false, false)
