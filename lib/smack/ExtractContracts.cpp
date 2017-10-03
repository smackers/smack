//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "contracts"

#include "smack/SmackOptions.h"
#include "smack/Naming.h"
#include "smack/ExtractContracts.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "smack/Debug.h"

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

  Value* getVariable(Value* V) {
    if (auto I = dyn_cast<CallInst>(V)) {
      if (auto F = I->getCalledFunction()) {
        if (F->getName().find("__CONTRACT_int_variable") != std::string::npos) {
          assert(I->getNumArgOperands() == 1 && "Unexpected operands.");
          return I->getArgOperand(0);
        }
      }
    }
    return nullptr;
  }

  std::string getBinding(Value* V) {
    if (auto I = dyn_cast<CallInst>(V)) {
      if (auto F = I->getCalledFunction()) {
        auto name = F->getName();
        if (name == Naming::CONTRACT_FORALL ||
            name == Naming::CONTRACT_EXISTS) {
          return getString(I->getArgOperand(0));
        }
      }
    }
    return "";
  }

  Function* projection(Function* F, Type* T,
    std::vector<Value*>& arguments, std::map<Value*, Value*>& clones) {

    std::vector<Type*> parameters;
    for (auto A : arguments)
      parameters.push_back(A->getType());

    auto FF = Function::Create(
      FunctionType::get(T, parameters, false),
      GlobalValue::InternalLinkage, Naming::CONTRACT_EXPR, F->getParent());

    FF->setDoesNotAccessMemory();

    FF->getArgumentList().clear();
    for (auto A : arguments) {
      auto P = dyn_cast<Argument>(clones[A]);
      FF->getArgumentList().push_back(P);
      if (auto S = getVariable(A)) {
        AttributeSet Ax;
        P->addAttr(Ax.addAttribute(A->getContext(), 1, "contract-var", getString(S)));
      }
    }

    for (auto& B : *F) {
      if (clones.count(&B)) {
        auto BB = dyn_cast<BasicBlock>(clones[&B]);
        for (auto& I : B) {
          if (clones.count(&I) && clones[&I]) {
            if (auto II = dyn_cast<Instruction>(clones[&I])) {
              if (!II->getParent()) {

                // Add the block if it’s not already
                if (!BB->size())
                  FF->getBasicBlockList().push_back(BB);

                BB->getInstList().push_back(II);
              }
            }
          } else if (auto T = dyn_cast<TerminatorInst>(&I)) {
            if (!clones.count(T)) {

              // TODO filter out targets not in the projection, i.e., to avoid
              // failing the assertion below.

              auto TT = T->clone();
              for (auto& O : TT->operands()) {
                assert(clones.count(O.get()) && "Unvisited block.");
                O.set(clones[O.get()]);
              }

              // Add the block if it’s not already
              if (!BB->size())
                FF->getBasicBlockList().push_back(BB);

              BB->getInstList().push_back(TT);
            }
          }
        }
      }
    }
    return FF;
  }

  Function* extractedFunction(Value* V, BasicBlock* B,
    std::vector<Value*>& arguments, std::map<Value*, Value*>& clones) {

    auto &C = V->getContext();
    auto R = ReturnInst::Create(C, clones[V], dyn_cast<BasicBlock>(clones[B]));
    R->removeFromParent();
    clones[B->getTerminator()] = R;
    return projection(B->getParent(), V->getType(), arguments, clones);
  }
}

void ExtractContracts::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<LoopInfoWrapperPass>();
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

      if (auto J = dyn_cast<CallInst>(I.getArgOperand(0)))
        if (auto G = J->getCalledFunction())
          if (G->getName().find(Naming::CONTRACT_EXPR) != std::string::npos)
            return;

      Function* EF;
      std::vector<Value*> Args;
      tie(EF, Args) = extractExpression(I.getArgOperand(0), I.getParent());
      I.setArgOperand(0, CallInst::Create(EF, Args, "", &I));
      modified = true;

      // TODO can we somehow force LLVM to consider calls to the obsoleted
      // forall, exists, etc., to be dead code?

    } else if (name == Naming::CONTRACT_FORALL ||
               name == Naming::CONTRACT_EXISTS) {

      if (auto J = dyn_cast<CallInst>(I.getArgOperand(1)))
        if (auto G = J->getCalledFunction())
          if (G->getName().find(Naming::CONTRACT_EXPR) != std::string::npos)
            return;

      Function* EF;
      std::vector<Value*> Args;
      tie(EF, Args) = extractExpression(I.getArgOperand(1), I.getParent());
      I.setArgOperand(1, CallInst::Create(EF, Args, "", &I));
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
  auto& LI = getAnalysis<LoopInfoWrapperPass>(*F).getLoopInfo();
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

  std::vector<std::string> captures;
  auto var = getBinding(V);
  if (var != "")
    captures.push_back(var);

  DEBUG(errs() << "[contracts]"
    << " extracting " << *V
    << " from " << E->getParent()->getName()
    << ":" << E->getName() << "\n");

  auto &C = V->getContext();

  std::stack<Value*> value_stack;
  std::map<Value*, Value*> clones;
  std::map<Value*, Value*> variables;
  std::vector<Value*> arguments;

  value_stack.push(V);
  value_stack.push(E);
  clones[E->getTerminator()] = nullptr;

  while (!value_stack.empty()) {
    Value* V = value_stack.top();

    if (!clones.count(V)) {

      DEBUG(errs() << "[contracts]"
        << " (" << value_stack.size() << ")"
        << " entering " << *V << "\n");

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

      DEBUG(errs() << "[contracts]"
        << " (" << value_stack.size() << ")"
        << " leaving " << *V << "\n");

      if (auto B = dyn_cast<BasicBlock>(V)) {
        clones[B] = BasicBlock::Create(C, B->getName());

      } else if (auto X = getVariable(V)) {
        if (!variables.count(X)) {
          if (std::find(captures.begin(), captures.end(), getString(X)) != captures.end()) {
            auto I = dyn_cast<Instruction>(V);
            assert(I && "Expected instruction.");
            variables[X] = I->clone();
          } else {
            variables[X] = new Argument(V->getType(), getString(X));
            arguments.push_back(V);
          }
        }
        clones[V] = variables[X];

      } else if (hasDominatedIncomingValue(V) ||
                 isa<Argument>(V) ||
                 (isa<GlobalValue>(V) && !isa<Function>(V))) {
        clones[V] = new Argument(V->getType(), V->getName());
        arguments.push_back(V);

      } else if (isa<StoreInst>(V)) {
        llvm_unreachable("Unexpected store instruction!");

      } else if (auto I = dyn_cast<Instruction>(V)) {
        assert(clones.count(I->getParent()) && "Forgot to visit parent block.");
        assert(clones[I->getParent()] != I->getParent() && "Forgot to clone parent block.");

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

  return std::make_tuple(
    extractedFunction(V, E, arguments, clones),
    arguments);
}

// Pass ID variable
char ExtractContracts::ID = 0;

// Register the pass
static RegisterPass<ExtractContracts>
X("extract-contracts", "Extract Contracts");

}
