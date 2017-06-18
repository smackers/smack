//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "contracts"

#include "smack/SmackOptions.h"
#include "smack/Naming.h"
#include "smack/VerifierCodeMetadata.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"

#include <vector>
#include <stack>
#include <map>
#include <set>

namespace smack {

using namespace llvm;

namespace {
  std::string getString(const llvm::Value* v) {
    if (const llvm::ConstantExpr* constantExpr = llvm::dyn_cast<const llvm::ConstantExpr>(v))
      if (constantExpr->getOpcode() == llvm::Instruction::GetElementPtr)
        if (const llvm::GlobalValue* cc = llvm::dyn_cast<const llvm::GlobalValue>(constantExpr->getOperand(0)))
          if (const llvm::ConstantDataSequential* cds = llvm::dyn_cast<const llvm::ConstantDataSequential>(cc->getOperand(0)))
            return cds ->getAsCString();
    return "";
  }

  void mark(Instruction &I, bool V = true) {
    auto& C = I.getContext();
    I.setMetadata("verifier.code",
      MDNode::get(C, ConstantAsMetadata::get(
        V ? ConstantInt::getTrue(C) : ConstantInt::getFalse(C)
      )));
  }

  bool isMarked(Instruction& I) {
    auto *N = I.getMetadata("verifier.code");
    assert(N->getNumOperands() == 1);
    auto *M = dyn_cast<ConstantAsMetadata>(N->getOperand(0).get());
    auto *C = dyn_cast<ConstantInt>(M->getValue());
    return C->isOne();
  }
}

void VerifierCodeMetadata::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
}

bool VerifierCodeMetadata::runOnModule(Module &M) {
  visit(M);
  while (!workList.empty()) {
    auto &I = *workList.front();
    for (auto V : I.operand_values()) {
      if (auto J = dyn_cast<Instruction>(V)) {
        if (!isMarked(*J) && !dyn_cast<CallInst>(J)) {
          auto onlyVerifierUsers = true;
          std::queue<User*> users;
          for (auto U : J->users())
            users.push(U);

          while (!users.empty()) {
            if (auto K = dyn_cast<Instruction>(users.front())) {
              if (!isMarked(*K)) {
                onlyVerifierUsers = false;
                break;
              }
            } else {
              for (auto UU : users.front()->users())
                users.push(UU);
            }
            users.pop();
          }
          if (onlyVerifierUsers) {
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
  if (auto F = I.getCalledFunction()) {
    auto name = F->getName();
    auto V = name.find("__VERIFIER_") == 0;
    mark(I, V);
    if (V) workList.push(&I);
  }
}

void VerifierCodeMetadata::visitInstruction(Instruction &I) {
  mark(I, false);
}

// Pass ID variable
char VerifierCodeMetadata::ID = 0;

// Register the pass
static RegisterPass<VerifierCodeMetadata>
X("verifier-code-metadata", "Verifier Code Metadata");

}
