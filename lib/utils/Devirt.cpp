//===- Devirt.cpp - Devirtualize indirect function calls via SVF ----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Rewrites each indirect call `(*fp)(args)` whose targets SVF resolves
// COMPLETELY into a direct dispatch over those targets (a "bounce" function),
// so SMACK's translator -- which cannot emit a genuine indirect call -- can
// handle function-pointer / vtable code. The target set comes from SVF's
// Andersen call graph (`getIndCSCallees`); the rewrite only fires when SVF
// proves the function pointer points *only* to known functions (its points-to
// set excludes the black-hole), which is exactly what makes the bounce's
// `unreachable` no-match branch sound. Unresolvable callsites are left as-is.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "devirt"

#include "utils/Devirt.h"
#include "utils/InitializePasses.h"

#include "smack/DSAWrapper.h"
#include "smack/DSAWrapperAnalysis.h"
#include "smack/InitializePasses.h"
#include "smack/Debug.h"
#include "smack/LlvmCompat.h"
#include "smack/SmackOptions.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/raw_ostream.h"

// SVF: the (sound) source of indirect-call targets. Reused from the analysis
// DSAWrapper builds once; see DSAWrapper::cachedSVF.
#include "Graphs/CallGraph.h"
#include "Graphs/ICFGNode.h"
#include "MemoryModel/PointsTo.h"
#include "SVF-LLVM/LLVMModule.h"
#include "SVFIR/SVFIR.h"
#include "SVFIR/SVFVariables.h"
#include "WPA/Andersen.h"

#include <algorithm>
#include <set>
#include <string>
#include <vector>

using namespace llvm;

// Pass statistics
STATISTIC(FuncAdded, "Number of bounce functions added");
STATISTIC(CSConvert, "Number of call sites converted");

static cl::opt<std::string> DevirtReportFilename(
    "smack-devirt-report",
    cl::desc("Output SMACK devirtualization target report as JSON"),
    cl::init(""), cl::value_desc("filename"));

//===----------------------------------------------------------------------===//
// IR-rewrite helpers (unchanged from the original devirt pass).
//===----------------------------------------------------------------------===//

//
// Return a pointer to the LLVM type for a void pointer.
//
static inline PointerType *getVoidPtrType(LLVMContext &C) {
  Type *Int8Type = IntegerType::getInt8Ty(C);
  return PointerType::getUnqual(Int8Type);
}

//
// Given an LLVM value, insert a cast instruction to make it a given type.
//
static inline Value *castTo(Value *V, Type *Ty, std::string Name,
                            Value *InsertPt) {
  // Don't bother creating a cast if it's already the correct type.
  if (V->getType() == Ty)
    return V;

  // If it's a constant, just create a constant expression.
  if (Constant *C = dyn_cast<Constant>(V)) {
    Constant *CE = nullptr;
    if (C->getType()->isIntegerTy() && Ty->isIntegerTy()) {
      auto srcBits = C->getType()->getIntegerBitWidth();
      auto dstBits = Ty->getIntegerBitWidth();
      CE = srcBits == dstBits
               ? C
               : ConstantExpr::getCast(srcBits < dstBits ? Instruction::ZExt
                                                         : Instruction::Trunc,
                                       C, Ty);
    } else
      CE = ConstantExpr::getBitCast(C, Ty);
    return CE;
  }

  // Otherwise, insert a cast instruction.
  if (auto I = dyn_cast<Instruction>(InsertPt))
    return CastInst::CreateZExtOrBitCast(V, Ty, Name, I);
  else if (auto B = dyn_cast<BasicBlock>(InsertPt))
    return CastInst::CreateZExtOrBitCast(V, Ty, Name, B);
  else
    llvm_unreachable("Unexpected insertion point.");
}

static inline bool isZExtOrBitCastable(Value *V, Type *T) {
  return CastInst::castIsValid(Instruction::ZExt, V->getType(), T) ||
         CastInst::castIsValid(Instruction::BitCast, V->getType(), T);
}

//
// Is target F callable at call site CS with (at most ZExt/BitCast) argument
// adaptation? The bounce performs these casts, so an incompatible target could
// not be dispatched -- such a target forces us to leave the callsite untouched
// (see resolveSVFTargets) rather than silently drop a possible runtime target.
//
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

  for (unsigned i = 0; i < M; i++) {
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

  for (unsigned i = 0; i < N; i++) {
    auto A = CS->getArgOperand(i);
    auto PT = T->getParamType(i + 1);
    if (A->getType() != PT && !isZExtOrBitCastable(A, PT))
      return false;
  }
  return true;
}

// SMACK's value-tracking intrinsic is never a real runtime function-pointer
// target, so it is skipped (without making the resolution "incomplete").
static bool isIgnoredTarget(const Function &F) {
  return F.getName() == "__SMACK_value";
}

static std::vector<const Function *>
sortedTargets(const std::set<const Function *> &targets) {
  std::vector<const Function *> out(targets.begin(), targets.end());
  std::sort(out.begin(), out.end(), [](const Function *lhs, const Function *rhs) {
    return lhs->getName() < rhs->getName();
  });
  return out;
}

//===----------------------------------------------------------------------===//
// SVF target resolution + soundness completeness gate.
//===----------------------------------------------------------------------===//

namespace {

struct SvfResolution {
  // True only when SVF resolved EVERY possible target (no black-hole) and each
  // maps to a signature-compatible llvm::Function -- the precondition for a
  // sound `unreachable` no-match branch. Devirt fires iff this is true.
  bool complete = false;
  std::vector<const Function *> targets;
  std::string reason; // diagnostic: why complete / why not
};

//
// Resolve the targets of indirect call CS from SVF's Andersen call graph.
//
// Soundness: we devirtualize ONLY when the resolution is complete, i.e. SVF
// proves the function pointer points only to known functions. The gate is:
//   (1) SVF has resolved callees for this site (hasIndCSCallees), AND
//   (2) the function pointer's points-to set excludes the black-hole (SVF's
//       "points to some unknown object" marker), AND
//   (3) every resolved callee maps to a signature-compatible llvm::Function.
// If any callee cannot be mapped or matched, we BAIL (mark incomplete) rather
// than drop a possible target -- dropping one would make the bounce's
// `unreachable` reachable at runtime, which is unsound.
//
SvfResolution resolveSVFTargets(CallBase *CS) {
  SvfResolution R;
  Module &M = *CS->getModule();

  SVF::LLVMModuleSet *ms = nullptr;
  SVF::SVFIR *pag = nullptr;
  SVF::Andersen *ander = nullptr;
  if (!smack::DSAWrapper::cachedSVF(ms, pag, ander) || !ms || !pag || !ander) {
    R.reason = "svf-unavailable";
    return R;
  }

  SVF::CallICFGNode *cnode = ms->getCallICFGNode(CS);
  if (!cnode) {
    R.reason = "no-icfg-node";
    return R;
  }

  if (!ander->hasIndCSCallees(cnode)) {
    R.reason = "svf-no-callees";
    return R;
  }

  // Completeness gate (the crux): the function pointer must point only to known
  // objects. If its points-to set contains the black-hole, SVF could not bound
  // the target set, so the `unreachable` fallback would be unsound -> leave the
  // call untouched.
  const SVF::SVFVar *funPtr = cnode->getIndFunPtr();
  if (!funPtr) {
    R.reason = "no-fun-ptr";
    return R;
  }
  const SVF::PointsTo &pts = ander->getPts(funPtr->getId());
  if (pts.empty()) {
    R.reason = "empty-pts";
    return R;
  }
  if (pts.test(pag->getBlackHoleNode())) {
    R.reason = "black-hole";
    return R;
  }

  // Map each resolved callee to its llvm::Function.
  std::set<const Function *> resolved;
  for (const SVF::FunObjVar *fo : ander->getIndCSCallees(cnode)) {
    const std::string &name = fo->getName();
    Function *F = M.getFunction(name);
    if (!F) {
      R.reason = "target-unmapped:" + name;
      return R;
    }
    if (isIgnoredTarget(*F))
      continue;
    if (!match(CS, *F)) {
      R.reason = "target-type-mismatch:" + name;
      return R;
    }
    resolved.insert(F);
  }
  if (resolved.empty()) {
    R.reason = "no-usable-targets";
    return R;
  }

  R.targets = sortedTargets(resolved);
  R.complete = true;
  R.reason = "svf-complete";
  return R;
}

} // namespace

//===----------------------------------------------------------------------===//
// Optional JSON report (consumed by the devirt validation oracle).
//===----------------------------------------------------------------------===//

namespace {

struct DevirtReportEntry {
  std::string callsiteId;
  unsigned callsiteIndex = 0;
  std::string function;
  std::string file;
  unsigned line = 0;
  unsigned column = 0;
  std::string instruction;
  bool complete = false;
  unsigned targetCount = 0;
  std::string reason;
  std::vector<std::string> targets;
};

std::vector<DevirtReportEntry> DevirtReportEntries;
std::map<const CallBase *, unsigned> DevirtCallsiteIndices;

std::string valueToString(const Value &V) {
  std::string out;
  raw_string_ostream os(out);
  V.print(os);
  return os.str();
}

unsigned indirectCallsiteIndex(const CallBase &CS) {
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

std::string makeCallsiteId(const CallBase &CS, unsigned index) {
  std::string function = CS.getFunction()->getName().str();
  return function + ":indirect:" + std::to_string(index);
}

void addDebugLoc(DevirtReportEntry &entry, const CallBase &CS) {
  if (const DebugLoc &loc = CS.getDebugLoc()) {
    entry.line = loc.getLine();
    entry.column = loc.getCol();
    if (const auto *scope = dyn_cast_or_null<DIScope>(loc.getScope()))
      entry.file = scope->getFilename().str();
  }
}

void recordDevirtResolution(const CallBase &CS,
                            const SvfResolution &resolution) {
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
  entry.complete = resolution.complete;
  entry.targetCount = resolution.targets.size();
  entry.reason = resolution.reason;
  addDebugLoc(entry, CS);
  for (const Function *F : resolution.targets)
    entry.targets.push_back(F->getName().str());
  DevirtReportEntries.push_back(std::move(entry));
}

void writeDevirtReport(const Module &M) {
  if (DevirtReportFilename.empty())
    return;

  std::error_code EC;
  ToolOutputFile F(DevirtReportFilename.c_str(), EC, sys::fs::OF_Text);
  if (EC) {
    errs() << "Could not write " << DevirtReportFilename << ": " << EC.message()
           << "\n";
    return;
  }

  json::OStream J(F.os(), 2);
  J.object([&] {
    J.attribute("schema_version", 3);
    J.attribute("module", M.getModuleIdentifier());
    J.attribute("target_source", "svf");
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
          J.attribute("complete", entry.complete);
          J.attribute("target_count", entry.targetCount);
          J.attribute("reason", entry.reason);
          J.attributeArray("targets", [&] {
            for (const auto &target : entry.targets)
              J.value(target);
          });
        });
      }
    });
  });
  F.keep();
}

} // namespace

//===----------------------------------------------------------------------===//
// The bounce-function rewrite (unchanged from the original devirt pass).
//===----------------------------------------------------------------------===//

//
// Method: buildBounce()
//
// Description:
//  Builds a bounce function that compares the incoming function pointer to each
//  target and, on a match, performs the direct call; on no match it executes
//  `unreachable` (sound because the caller only devirtualizes COMPLETE sites).
//
Function *Devirtualize::buildBounce(CallBase *CS,
                                    std::vector<const Function *> &Targets) {
  // Update the statistics on the number of bounce functions added.
  ++FuncAdded;
  // Create a bounce function whose signature matches the call, plus an extra
  // leading pointer argument carrying the function pointer to dispatch on.
  Value *ptr = CS->getCalledOperand();
  std::vector<Type *> TP;
  TP.insert(TP.begin(), ptr->getType());
  for (auto i = CS->arg_begin(); i != CS->arg_end(); ++i) {
    TP.push_back((*i)->getType());
  }

  FunctionType *NewTy = FunctionType::get(CS->getType(), TP, false);
  Module *M = CS->getParent()->getParent()->getParent();
  Function *F =
      Function::Create(NewTy, GlobalValue::InternalLinkage, "devirtbounce", M);

  // Set the names of the arguments.
  F->arg_begin()->setName("funcPtr");
  for (auto A = std::next(F->arg_begin()), E = F->arg_end(); A != E; ++A)
    A->setName("arg");

  // Create an entry basic block.
  BasicBlock *entryBB = BasicBlock::Create(M->getContext(), "entry", F);

  // For each function target, create a basic block that calls it directly.
  std::map<const Function *, BasicBlock *> targets;
  for (unsigned index = 0; index < Targets.size(); ++index) {
    const Function *FL = Targets[index];
    const FunctionType *FT = FL->getFunctionType();

    // Create the basic block for doing the direct call.
    BasicBlock *BL = BasicBlock::Create(M->getContext(), FL->getName(), F);
    targets[FL] = BL;

    // Create the direct function call.
    std::vector<Value *> Args;
    Function::arg_iterator P, PE;
    FunctionType::param_iterator T, TE;
    for (P = std::next(F->arg_begin()), PE = F->arg_end(), T = FT->param_begin(),
        TE = FT->param_end();
         P != PE && T != TE; ++P, ++T)
      Args.push_back(castTo(&*P, *T, "", BL));

    Value *directCall = CallInst::Create(const_cast<Function *>(FL), Args, "", BL);

    // Add the return instruction for the basic block.
    if (CS->getType()->isVoidTy())
      ReturnInst::Create(M->getContext(), BL);
    else
      ReturnInst::Create(M->getContext(), directCall, BL);
  }

  // Create a failure basic block ending in `unreachable`.
  BasicBlock *failBB = BasicBlock::Create(M->getContext(), "fail", F);

  if (Targets.size())
    new UnreachableInst(M->getContext(), failBB);
  else
    ReturnInst::Create(M->getContext(), failBB);

  // Entry block initially branches to the failure block; rewired below.
  BranchInst *InsertPt = BranchInst::Create(failBB, entryBB);

  // Build the comparison chain over the function pointer.
  Type *VoidPtrType = getVoidPtrType(M->getContext());
  Value *FArg = castTo(&*F->arg_begin(), VoidPtrType, "", InsertPt);
  BasicBlock *tailBB = failBB;
  for (unsigned index = 0; index < Targets.size(); ++index) {
    Value *TargetInt = castTo(const_cast<Function *>(Targets[index]),
                              VoidPtrType, "", InsertPt);

    BasicBlock *TB = targets[Targets[index]];
    BasicBlock *newB = BasicBlock::Create(
        M->getContext(), "test." + Targets[index]->getName(), F);
    CmpInst *setcc = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ,
                                     TargetInt, FArg, "sc", newB);
    BranchInst::Create(TB, tailBB, setcc, newB);

    tailBB = newB;
  }

  // Make the entry block branch to the first comparison block.
  InsertPt->setSuccessor(0, tailBB);
  return F;
}

//
// Method: findInCache()
//
// Looks for an existing bounce function reusable for this call site.
//
const Function *Devirtualize::findInCache(const CallBase *CS,
                                          std::set<const Function *> &Targets) {
  std::map<const Function *, std::set<const Function *>>::iterator I;
  for (I = bounceCache.begin(); I != bounceCache.end(); ++I) {
    const Function *bounceFunc = I->first;

    // Check the return type.
    if (CS->getType() != bounceFunc->getReturnType())
      continue;

    // Check the type of the function pointer and the arguments.
    PointerType *PT = dyn_cast<PointerType>(bounceFunc->arg_begin()->getType());
    assert(PT);
    if (CS->getCalledOperand()->stripPointerCastsAndAliases()->getType() != PT)
      continue;

    FunctionType *FT = CS->getFunctionType();
    if (FT->isVarArg() && !checkArgs(CS, bounceFunc))
      continue;

    // Determine whether the targets are identical.
    if (Targets == I->second)
      return I->first;
  }

  return 0;
}

//
// Method: makeDirectCall()
//
// Transforms the specified indirect call site into a direct call, IF SVF
// resolves it completely; otherwise leaves it untouched.
//
void Devirtualize::makeDirectCall(CallBase *CS) {
  SvfResolution resolution = resolveSVFTargets(CS);
  recordDevirtResolution(*CS, resolution);

  // Soundness gate: only devirtualize completely-resolved call sites, so the
  // bounce's `unreachable` no-match branch is genuinely infeasible.
  if (!resolution.complete || resolution.targets.empty())
    return;

  std::vector<const Function *> Targets = resolution.targets;
  std::set<const Function *> targetSet(Targets.begin(), Targets.end());
  const Function *NF = findInCache(CS, targetSet);

  if (!NF) {
    NF = buildBounce(CS, Targets);
    bounceCache[NF] = targetSet;
  }

  // Replace the original call with a call to the bounce function.
  if (CallInst *CI = dyn_cast<CallInst>(CS)) {
    std::vector<Value *> Params;
    Params.push_back(CI->getCalledOperand());
    for (unsigned i = 0; i < CI->arg_size(); i++) {
      Params.push_back(castTo(CI->getArgOperand(i),
                              NF->getFunctionType()->getParamType(i + 1), "",
                              CS));
    }

    std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
    CallInst *CN = CallInst::Create(const_cast<Function *>(NF), Params, name, CI);
    CI->replaceAllUsesWith(CN);
    CI->eraseFromParent();
  } else if (InvokeInst *CI = dyn_cast<InvokeInst>(CS)) {
    std::vector<Value *> Params;
    Params.push_back(CI->getCalledOperand());
    for (unsigned i = 0; i < CI->arg_size(); i++)
      Params.push_back(castTo(CI->getArgOperand(i),
                              NF->getFunctionType()->getParamType(i + 1), "",
                              CS));
    std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
    InvokeInst *CN =
        InvokeInst::Create(const_cast<Function *>(NF), CI->getNormalDest(),
                           CI->getUnwindDest(), Params, name, CI);
    CI->replaceAllUsesWith(CN);
    CI->eraseFromParent();
  }

  // Update the statistics on the number of transformed call sites.
  ++CSConvert;
}

//
// Method: processCallSite()
//
// If CS is an indirect call, queue it for transformation. Whether it is
// actually devirtualized is decided in makeDirectCall (completeness gate).
//
void Devirtualize::processCallSite(CallBase *CS) {
  if (!CS->isIndirectCall())
    return;

  DevirtCallsiteIndices[CS] = Worklist.size();
  Worklist.push_back(CS);
}

//
// Method: runOnModule()
//
// Entry point: find indirect calls and turn the completely-resolved ones into
// direct calls.
//
bool Devirtualize::runOnModule(Module &M) {
  Worklist.clear();
  DevirtCallsiteIndices.clear();
  if (!DevirtReportFilename.empty())
    DevirtReportEntries.clear();

  TD = &M.getDataLayout();

  // Collect indirect call sites, then transform.
  visit(M);
  for (unsigned index = 0; index < Worklist.size(); ++index)
    makeDirectCall(Worklist[index]);

  writeDevirtReport(M);

  // Conservatively assume we've changed one or more call sites.
  return true;
}

void Devirtualize::getAnalysisUsage(AnalysisUsage &AU) const {
  // Forces DSAWrapper (which builds the SVF analysis devirt reuses) to run
  // first. We only need the side effect -- the SVF singletons -- which we read
  // via DSAWrapper::cachedSVF.
  AU.addRequired<smack::DSAWrapper>();
}

// Pass ID variable
char Devirtualize::ID = 0;

llvm::PreservedAnalyses
DevirtualizeNewPM::run(Module &M, ModuleAnalysisManager &MAM) {
  // Ensure SVF is built (DSAWrapperAnalysis caches it) before devirt resolves.
  MAM.getResult<smack::DSAWrapperAnalysis>(M);
  Devirtualize pass;
  bool changed = pass.runOnModule(M);
  return changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

using namespace smack;
// Pass registration
INITIALIZE_PASS_BEGIN(Devirtualize, "devirt",
                      "Devirtualize indirect function calls", false, false)
INITIALIZE_PASS_DEPENDENCY(DSAWrapper)
INITIALIZE_PASS_END(Devirtualize, "devirt",
                    "Devirtualize indirect function calls", false, false)
