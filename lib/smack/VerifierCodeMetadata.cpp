//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "verifier-code-metadata"

#include "smack/VerifierCodeMetadata.h"
#include "smack/Debug.h"
#include "smack/SmackOptions.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/DataLayout.h"

#include <set>

namespace smack {

using namespace llvm;

namespace {
void mark(Instruction &I, bool V = true) {
  auto &C = I.getContext();
  I.setMetadata(
      "verifier.code",
      MDNode::get(C, ConstantAsMetadata::get(V ? ConstantInt::getTrue(C)
                                               : ConstantInt::getFalse(C))));
}

void markVerifierPrimitive(CallInst &I, StringRef Primitive) {
  auto &C = I.getContext();
  I.setMetadata("verifier.primitive",
                MDNode::get(C, MDString::get(C, Primitive)));
}

bool isVerifierFunctionCall(CallInst &I) {
  if (auto F = I.getCalledFunction()) {
    auto N = F->getName();

    if (N.find("__VERIFIER_") == 0)
      return true;

    if (N.find("__SMACK_") == 0)
      return true;

    if (N.find("__CONTRACT_") == 0)
      return true;
  }
  return false;
}

bool onlyVerifierUsers(Instruction &I) {
  std::queue<User *> users;
  std::set<User *> known;

  for (auto U : I.users()) {
    users.push(U);
    known.insert(U);
  }

  while (!users.empty()) {
    if (auto K = dyn_cast<Instruction>(users.front())) {
      if (!VerifierCodeMetadata::isMarked(*K))
        return false;

    } else {
      for (auto UU : users.front()->users()) {
        if (known.count(UU) == 0) {
          users.push(UU);
          known.insert(UU);
        }
      }
    }
    users.pop();
  }
  return true;
}
} // namespace

bool VerifierCodeMetadata::isMarked(const Instruction &I) {
  auto *N = I.getMetadata("verifier.code");
  assert(N && "expected metadata");
  assert(N->getNumOperands() == 1);
  auto *M = dyn_cast<ConstantAsMetadata>(N->getOperand(0).get());
  assert(M && "expected constant-valued metadata");
  auto *C = dyn_cast<ConstantInt>(M->getValue());
  assert(C && "expected constant-int-valued metadata");
  return C->isOne();
}

StringRef VerifierCodeMetadata::getVerifierPrimitive(const CallInst &I) {
  auto *N = I.getMetadata("verifier.primitive");
  if (!N || N->getNumOperands() != 1)
    return {};
  auto *S = dyn_cast<MDString>(N->getOperand(0).get());
  return S ? S->getString() : StringRef();
}

void VerifierCodeMetadata::getAnalysisUsage(AnalysisUsage &AU) const {}

bool VerifierCodeMetadata::runOnModule(Module &M) {

  verifierPrimitives.clear();
  if (auto *Annotations = M.getNamedGlobal("llvm.global.annotations"))
    if (auto *Array = dyn_cast<ConstantArray>(Annotations->getInitializer()))
      for (const Use &Operand : Array->operands()) {
        auto *Entry = dyn_cast<ConstantStruct>(Operand.get());
        if (!Entry || Entry->getNumOperands() < 2)
          continue;
        auto *F = dyn_cast<Function>(
            Entry->getOperand(0)->stripPointerCastsAndAliases());
        StringRef Annotation;
        if (!F || !getConstantStringInfo(Entry->getOperand(1), Annotation))
          continue;
        StringRef Prefix = "smack.verifier.";
        if (!Annotation.startswith(Prefix))
          continue;
        StringRef Primitive = Annotation.drop_front(Prefix.size());
        if (Primitive == "assert" || Primitive == "assume")
          verifierPrimitives[F] = Primitive.str();
      }

  // The SV-COMP frontend force-includes smack.h before the task.  Tasks define
  // __VERIFIER_assert themselves with either an int or _Bool parameter, so a
  // typed annotated declaration in the header would conflict with one of the
  // two families.  Under this explicit frontend contract, attach the same
  // primitive identity by reserved name after Clang has preserved the task's
  // actual function type.  Other frontends still require an annotation.
  if (SmackOptions::SVComp) {
    if (auto *F = M.getFunction("__VERIFIER_assert"))
      verifierPrimitives[F] = "assert";
    if (auto *F = M.getFunction("__VERIFIER_assume"))
      verifierPrimitives[F] = "assume";
  }

  // first mark verifier function calls
  visit(M);

  // then mark values which flow only into marked instructions
  while (!workList.empty()) {
    auto &I = *workList.front();
    for (auto V : I.operand_values()) {
      if (auto J = dyn_cast<Instruction>(V)) {
        if (!isMarked(*J) && !dyn_cast<CallInst>(J)) {
          if (onlyVerifierUsers(*J)) {
            mark(*J);
            workList.push(J);
          }
        }
      }
    }
    workList.pop();
  }

  return true;
}

void VerifierCodeMetadata::visitCallInst(CallInst &I) {
  auto marked = false;

  if (isVerifierFunctionCall(I)) {
    marked = true;
    workList.push(&I);
  }

  if (auto *F = I.getCalledFunction()) {
    auto Primitive = verifierPrimitives.find(F);
    if (Primitive != verifierPrimitives.end())
      markVerifierPrimitive(I, Primitive->second);
  }

  mark(I, marked);
}

void VerifierCodeMetadata::visitInstruction(Instruction &I) { mark(I, false); }

// Pass ID variable
char VerifierCodeMetadata::ID = 0;

// Register the pass
static RegisterPass<VerifierCodeMetadata> X("verifier-code-metadata",
                                            "Verifier Code Metadata");
} // namespace smack
