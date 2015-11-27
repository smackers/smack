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

std::tuple< Function*, std::vector<Value*> >
ExtractContracts::extractExpression(Value* V) {
  Module* M = (Module*) dyn_cast<Instruction>(V)->getParent()->getParent()->getParent();
  LLVMContext& C = V->getContext();
  BasicBlock* B = BasicBlock::Create(M->getContext(), "entry");

  // TODO handle multiple blocks
  // TODO handle phi nodes -- just like arguments

  std::stack<Value*> value_stack;
  std::map<Value*, Value*> clones;
  std::vector<Value*> arguments;
  std::vector<Type*> parameters;
  std::vector<BasicBlock*> blocks;

  blocks.push_back(B);

  value_stack.push(V);
  while (!value_stack.empty()) {
    Value* V = value_stack.top();
    if (clones.count(V)) {
      value_stack.pop();
      if (isa<StoreInst>(V)) {
        llvm_unreachable("Unexpected store instruction!");

      } else if (auto I = dyn_cast<Instruction>(V)) {
        auto II = I->clone();
        B->getInstList().push_back(II);
        for (auto& O : II->operands()) {
          assert(clones.count(O.get()));
          O.set(clones[O.get()]);
        }
        clones[I] = II;

      } else if (auto A = dyn_cast<Argument>(V)) {
        if (clones[A] == A) {
          clones[A] = new Argument(A->getType(), A->getName());
          parameters.push_back(A->getType());
          arguments.push_back(A);
        }
      } else if (auto G = dyn_cast<GlobalValue>(V)) {
        if (clones[G] == G) {
          clones[G] = new Argument(G->getType(), G->getName());
          parameters.push_back(G->getType());
          arguments.push_back(G);
        }
      }

    } else {
      clones[V] = V;
      if (auto U = dyn_cast<User>(V)) {
        for (auto& O : U->operands()) {
          value_stack.push(O.get());
        }
      }
    }
  }

  ReturnInst::Create(C, clones[V], B);
  Function* F = Function::Create(
    FunctionType::get(V->getType(), parameters, false),
    GlobalValue::InternalLinkage, Naming::CONTRACT_EXPR, M);
  F->getArgumentList().clear();
  for (auto A : arguments)
    F->getArgumentList().push_back((Argument*) clones[A]);
  for (auto B : blocks)
    F->getBasicBlockList().push_back(B);
  return std::make_tuple(F, arguments);
}

// Pass ID variable
char ExtractContracts::ID = 0;

// Register the pass
static RegisterPass<ExtractContracts>
X("extract-contracts", "Extract Contracts");

}
