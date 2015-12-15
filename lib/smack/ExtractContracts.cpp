//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "extract-contracts"

#include "smack/SmackOptions.h"
#include "smack/Naming.h"
#include "smack/ExtractContracts.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"

#include <vector>
#include <stack>
#include <map>
#include <set>

namespace smack {

using namespace llvm;

void ExtractContracts::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<LoopInfo>();
  AU.addRequired<DominatorTreeWrapperPass>();
}

bool ExtractContracts::runOnModule(Module& M) {
  modified = false;
  visit(M);
  return modified;
}

void ExtractContracts::visitCallInst(CallInst &I) {
  if (auto F = I.getCalledFunction()) {
    auto name = F->getName();
    if (name == Naming::CONTRACT_REQUIRES ||
        name == Naming::CONTRACT_ENSURES ||
        name == Naming::CONTRACT_INVARIANT) {
      validateAnnotation(I);
      Function* EF;
      std::vector<Value*> Args;
      tie(EF, Args) = extractExpression(I.getArgOperand(0), I.getParent());
      I.setArgOperand(0, CallInst::Create(EF, Args, "", &I));
      modified = true;
    }
  }
}

void ExtractContracts::validateAnnotation(CallInst &I) {
  assert(I.getCalledFunction() && "Unexpected virtual function.");
  assert(I.getNumArgOperands() == 1 && "Unexpected operands.");
  auto B = I.getParent();
  auto F = B->getParent();
  auto& DT = getAnalysis<DominatorTreeWrapperPass>(*F).getDomTree();
  auto& LI = getAnalysis<LoopInfo>(*F);
  if (I.getCalledFunction()->getName() == Naming::CONTRACT_INVARIANT) {
    auto L = LI[B];
    if (!L) {
      llvm_unreachable("Loop invariants must occur inside loops.");
    }
  } else {
    for (auto L : LI) {
      auto& J = L->getHeader()->getInstList().front();
      if (DT.dominates(&J, &I)) {
        llvm_unreachable("Procedure specifications must occur before loops.");
      }
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
ExtractContracts::extractExpression(Value* V, BasicBlock* E) {
  DEBUG(errs() << "[contracts]"
    << " extracting " << *V
    << " from " << E->getParent()->getName()
    << ":" << E->getName() << "\n");

  auto &C = V->getContext();
  auto F = E->getParent();
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
        auto B = I->getParent();
        assert(clones.count(B) && "Forgot to visit parent block.");
        assert(clones[B] != B && "Forgot to clone parent block.");

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
      }

    }

    value_stack.pop();
  }

  auto FF = Function::Create(
    FunctionType::get(V->getType(), parameters, false),
    GlobalValue::InternalLinkage, Naming::CONTRACT_EXPR, M);

  FF->getArgumentList().clear();
  for (auto A : arguments)
    FF->getArgumentList().push_back(dyn_cast<Argument>(clones[A]));

  for (auto& B : *F) {
    if (clones.count(&B)) {
      auto BB = dyn_cast<BasicBlock>(clones[&B]);
      FF->getBasicBlockList().push_back(BB);
      for (auto& I : B) {
        if (clones.count(&I)) {
          auto II = dyn_cast<Instruction>(clones[&I]);
          BB->getInstList().push_back(II);
        }
      }
    }
  }

  auto B = dyn_cast<BasicBlock>(clones[E]);
  ReturnInst::Create(C, clones[V], B);

  return std::make_tuple(FF, arguments);
}

// Pass ID variable
char ExtractContracts::ID = 0;

// Register the pass
static RegisterPass<ExtractContracts>
X("extract-contracts", "Extract Contracts");

}
