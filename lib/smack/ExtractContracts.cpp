//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "extract-contracts"

#include "smack/SmackOptions.h"
#include "smack/Naming.h"
#include "smack/ExtractContracts.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DataLayout.h"

#include <vector>
#include <stack>
#include <map>
#include <set>

namespace smack {

using namespace llvm;

bool ExtractContracts::runOnModule(Module& M) {
  TD = &getAnalysis<DataLayoutPass>().getDataLayout();
  visit(M);
  return true;
}

void ExtractContracts::visitCallInst(CallInst &I) {
  if (auto F = I.getCalledFunction()) {
    if (F->getName() == Naming::CONTRACT_REQUIRES ||
        F->getName() == Naming::CONTRACT_ENSURES ||
        F->getName() == Naming::CONTRACT_INVARIANT) {
      assert(I.getNumArgOperands() == 1 && "Unexpected operands to requires.");
      Function* EF;
      std::vector<Value*> Args;
      tie(EF, Args) = extractExpression(I.getArgOperand(0));
      I.setArgOperand(0, CallInst::Create(EF, Args, "", &I));

    }
  }
}

bool ExtractContracts::hasDominatedIncomingValue(Value* V) {
  if (auto PHI = dyn_cast<PHINode>(V)) {
    auto F = PHI->getParent()->getParent();
    const DominatorTree& DT =
      getAnalysis<DominatorTreeWrapperPass>(*F).getDomTree();
    for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++)
      if (auto I = dyn_cast<Instruction>(PHI->getIncomingValue(i)))
        if (DT.dominates(PHI, I))
          return true;
  }

  return false;
}

std::tuple< Function*, std::vector<Value*> >
ExtractContracts::extractExpression(Value* V) {
  auto R = dyn_cast<Instruction>(V);
  auto &C = V->getContext();
  auto F = R->getParent()->getParent();
  auto M = (Module*) F->getParent();

  std::stack<Value*> value_stack;
  std::map<Value*, Value*> clones;
  std::vector<Value*> arguments;
  std::vector<Type*> parameters;

  value_stack.push(V);

  while (!value_stack.empty()) {
    Value* V = value_stack.top();

    if (!clones.count(V)) {
      clones[V] = V;

      if (hasDominatedIncomingValue(V))
        continue;

      if (auto I = dyn_cast<Instruction>(V))
        value_stack.push(I->getParent());

      if (auto PHI = dyn_cast<PHINode>(V))
        for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++)
          value_stack.push(PHI->getIncomingBlock(i)->getTerminator());

      if (auto U = dyn_cast<User>(V))
        for (auto& O : U->operands())
          value_stack.push(O.get());

      continue;

    } else if (clones[V] == V) {

      if (auto B = dyn_cast<BasicBlock>(V)) {
        clones[B] = BasicBlock::Create(C, B->getName());

      } else if (hasDominatedIncomingValue(V) || isa<Argument>(V) || isa<GlobalValue>(V)) {
        clones[V] = new Argument(V->getType(), V->getName());
        parameters.push_back(V->getType());
        arguments.push_back(V);

      } else if (isa<StoreInst>(V)) {
        llvm_unreachable("Unexpected store instruction!");

      } else if (auto I = dyn_cast<Instruction>(V)) {
        auto II = I->clone();
        clones[I] = II;
        for (auto& O : II->operands()) {
          assert(clones.count(O.get()) && "Forgot to visit operand.");
          O.set(clones[O.get()]);
        }
        if (auto PHI = dyn_cast<PHINode>(II)) {
          for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
            auto B = PHI->getIncomingBlock(i);
            assert(clones.count(B) && "Forgot to visit incoming block.");
            assert(clones[B] != B && "Forgot to clone incoming block.");
            PHI->setIncomingBlock(i, dyn_cast<BasicBlock>(clones[B]));
          }
        }
        auto B = I->getParent();
        assert(clones.count(B) && "Forgot to visit parent block.");
        assert(clones[B] != B && "Forgot to clone parent block.");
        dyn_cast<BasicBlock>(clones[B])->getInstList().push_back(II);
      }

    }

    value_stack.pop();
  }

  ReturnInst::Create(C, clones[V],
    dyn_cast<BasicBlock>(clones[R->getParent()]));

  auto FF = Function::Create(
    FunctionType::get(V->getType(), parameters, false),
    GlobalValue::InternalLinkage, Naming::CONTRACT_EXPR, M);

  FF->getArgumentList().clear();
  for (auto A : arguments)
    FF->getArgumentList().push_back((Argument*) clones[A]);

  for (auto& B : *F)
    if (clones.count(&B))
      FF->getBasicBlockList().push_back(dyn_cast<BasicBlock>(clones[&B]));

  return std::make_tuple(FF, arguments);
}

// Pass ID variable
char ExtractContracts::ID = 0;

// Register the pass
static RegisterPass<ExtractContracts>
X("extract-contracts", "Extract Contracts");

}
