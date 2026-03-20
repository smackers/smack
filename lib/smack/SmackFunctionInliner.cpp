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

  unsigned instCount = getInstructionCount(F);
  if (involvesPointers(F))
    return instCount <= PtrInlineLimit;
  return InlineLimit > 0 && instCount <= InlineLimit;
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

    // Remove dead functions after inlining.
    if (inlinedAny) {
      std::vector<Function *> dead;
      for (Function &F : M) {
        if (F.isDeclaration())
          continue;
        if (F.use_empty() && !SmackOptions::isEntryPoint(F.getName()) &&
            F.getName().find("__SMACK_") == StringRef::npos &&
            F.getName().find("__VERIFIER_") == StringRef::npos) {
          dead.push_back(&F);
        }
      }
      for (auto *F : dead) {
        SDEBUG(errs() << "removing fully inlined: " << F->getName() << "\n");
        F->eraseFromParent();
      }
    }
  } while (inlinedAny);

  return changed;
}

char SmackFunctionInliner::ID = 0;

static RegisterPass<SmackFunctionInliner>
    X("smack-inline", "Inline small functions before DSA analysis");

} // namespace smack
