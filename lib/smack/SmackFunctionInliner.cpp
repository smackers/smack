//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "smack-inline"

#include "smack/SmackFunctionInliner.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <vector>

static llvm::cl::opt<bool>
    InlineFuncs("inline-funcs",
                llvm::cl::desc("Inline small functions before DSA analysis"),
                llvm::cl::init(false));

static llvm::cl::opt<unsigned>
    InlineLimit("inline-limit",
                llvm::cl::desc("Instruction count threshold for inlining "
                               "non-pointer functions (0 to disable)"),
                llvm::cl::init(50));

static llvm::cl::opt<unsigned>
    PtrInlineLimit("ptr-inline-limit",
                   llvm::cl::desc("Instruction count threshold for inlining "
                                  "pointer-involving functions"),
                   llvm::cl::init(200));

static llvm::cl::list<std::string>
    NoInlineFuncs("no-inline",
                  llvm::cl::desc("Functions that should not be inlined"),
                  llvm::cl::ZeroOrMore);

namespace smack {

using namespace llvm;

namespace {

Function *calledFunction(const CallBase &CB) {
  return dyn_cast<Function>(CB.getCalledOperand()->stripPointerCasts());
}

// The primitives whose string argument is copied into the Boogie program.
bool isBoogieText(StringRef name) {
  return name.find(Naming::CODE_PROC) != StringRef::npos ||
         name.find(Naming::DECL_PROC) != StringRef::npos ||
         name.find(Naming::TOP_DECL_PROC) != StringRef::npos ||
         name.find(Naming::MOD_PROC) != StringRef::npos;
}

bool isContract(StringRef name) {
  return name == Naming::CONTRACT_REQUIRES ||
         name == Naming::CONTRACT_ENSURES || name == Naming::CONTRACT_INVARIANT;
}

// The text of a string literal passed as an argument, or nothing.
StringRef literal(const Value *V) {
  auto *G = dyn_cast<GlobalVariable>(V->stripPointerCasts());
  if (!G || !G->hasInitializer())
    return StringRef();
  auto *D = dyn_cast<ConstantDataSequential>(G->getInitializer());
  return D && D->isString() ? D->getAsString() : StringRef();
}

// A body with Boogie text or a contract in it belongs to its function: a
// declaration would be emitted once for every copy of the body, and a contract
// would end up constraining the caller.
bool carriesBoogie(Function &F) {
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CB = dyn_cast<CallBase>(&I))
        if (Function *Callee = calledFunction(*CB))
          if (isBoogieText(Callee->getName()) || isContract(Callee->getName()))
            return true;
  return false;
}

} // namespace

bool SmackFunctionInliner::involvesPointers(Function &F) {
  if (F.getReturnType()->isPointerTy())
    return true;
  for (auto &Arg : F.args())
    if (Arg.getType()->isPointerTy())
      return true;
  return false;
}

unsigned SmackFunctionInliner::getInstructionCount(Function &F) {
  unsigned count = 0;
  for (auto &BB : F)
    count += BB.size();
  return count;
}

bool SmackFunctionInliner::shouldInline(Function &F) {
  if (F.isDeclaration() || F.isIntrinsic())
    return false;

  if (F.isVarArg())
    return false;

  auto name = F.getName();
  if (name.find("__SMACK_") != StringRef::npos)
    return false;
  if (name.find("__VERIFIER_") != StringRef::npos)
    return false;
  for (const auto &NI : NoInlineFuncs)
    if (name == NI)
      return false;
  if (SmackOptions::isEntryPoint(name))
    return false;

  if (recursiveFunctions.count(&F))
    return false;

  if (namedInBoogie.count(&F))
    return false;

  unsigned instCount = getInstructionCount(F);
  unsigned limit = involvesPointers(F) ? PtrInlineLimit : InlineLimit;
  if (limit == 0 || instCount > limit)
    return false;

  return !carriesBoogie(F);
}

// Boogie text can call a function by name, which leaves no trace in the IR.
// If every visible call to such a function were inlined, the function would
// look dead, be removed later in the pipeline, and leave that text calling a
// procedure that no longer exists. Matching on the name as a substring errs on
// the side of keeping a function.
void SmackFunctionInliner::computeNamedInBoogie(Module &M) {
  namedInBoogie.clear();
  std::vector<StringRef> texts;

  for (auto &F : M)
    for (auto &BB : F)
      for (auto &I : BB)
        if (auto *CB = dyn_cast<CallBase>(&I))
          if (Function *Callee = calledFunction(*CB))
            if (isBoogieText(Callee->getName()))
              for (auto &A : CB->args()) {
                StringRef text = literal(A);
                if (!text.empty())
                  texts.push_back(text);
              }

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (StringRef text : texts)
      if (text.contains(F.getName())) {
        namedInBoogie.insert(&F);
        break;
      }
  }
}

void SmackFunctionInliner::computeRecursiveFunctions(Module &M) {
  recursiveFunctions.clear();
  CallGraph CG(M);

  for (auto I = scc_begin(&CG); !I.isAtEnd(); ++I) {
    const auto &SCC = *I;
    if (SCC.size() > 1) {
      // Non-trivial SCC: all functions are mutually recursive
      for (auto *CGN : SCC)
        if (Function *F = CGN->getFunction())
          recursiveFunctions.insert(F);
    } else {
      // Single-node SCC: check for direct self-recursion
      CallGraphNode *CGN = SCC[0];
      Function *F = CGN->getFunction();
      if (F) {
        for (auto &CR : *CGN) {
          if (CR.second->getFunction() == F) {
            recursiveFunctions.insert(F);
            break;
          }
        }
      }
    }
  }
}

bool SmackFunctionInliner::runOnModule(Module &M) {
  if (!InlineFuncs)
    return false;

  // Property checks are selected by the function an instruction is in, which
  // is exactly what inlining changes. `smack` rejects the combination; this
  // covers llvm2bpl run on its own.
  if (!SmackOptions::CheckedFunctions.empty())
    return false;

  computeNamedInBoogie(M);

  bool changed = false;
  bool inlinedAny;

  do {
    inlinedAny = false;

    // Recompute recursive functions each iteration since inlining
    // may break cycles.
    computeRecursiveFunctions(M);

    // Build bottom-up order using the call graph SCCs.
    // scc_iterator yields SCCs in reverse topological order (callees before
    // callers), which is exactly the bottom-up order we want.
    CallGraph CG(M);
    std::vector<Function *> bottomUp;
    for (auto I = scc_begin(&CG); !I.isAtEnd(); ++I) {
      for (auto *CGN : *I)
        if (Function *F = CGN->getFunction())
          bottomUp.push_back(F);
    }

    // Process each function in bottom-up order: inline callees into it.
    for (Function *F : bottomUp) {
      if (F->isDeclaration())
        continue;

      // Collect inlineable call sites within this function.
      std::vector<CallBase *> callSites;
      for (auto &BB : *F) {
        for (auto &I : BB) {
          auto *CB = dyn_cast<CallBase>(&I);
          if (!CB)
            continue;

          Function *Callee = CB->getCalledFunction();
          if (!Callee)
            continue;

          if (!shouldInline(*Callee))
            continue;

          callSites.push_back(CB);
        }
      }

      // Inline collected call sites.
      for (auto *CB : callSites) {
        Function *Callee = CB->getCalledFunction();
        if (!Callee)
          continue;

        // Strip noinline attribute (added by -O0) since we inline for
        // analysis precision, not as a compiler optimization.
        Callee->removeFnAttr(Attribute::NoInline);

        InlineFunctionInfo IFI;
        InlineResult IR = InlineFunction(*CB, IFI);
        if (IR.isSuccess()) {
          SDEBUG(errs() << "inlined: " << Callee->getName() << "\n");
          inlinedAny = true;
          changed = true;
        }
      }
    }

    // A function left without callers is not removed here: RemoveDeadDefs
    // does that later in the pipeline, with the rules the rest of SMACK uses.
  } while (inlinedAny);

  return changed;
}

char SmackFunctionInliner::ID = 0;

static RegisterPass<SmackFunctionInliner>
    X("smack-inline", "Inline small functions before DSA analysis");

} // namespace smack
