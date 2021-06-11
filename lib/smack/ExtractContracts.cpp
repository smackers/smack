//
// This file is distributed under the MIT License. See LICENSE for details.
//

#define DEBUG_TYPE "contracts"

#include "smack/ExtractContracts.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"

#include <map>
#include <set>
#include <stack>
#include <vector>

namespace smack {

using namespace llvm;

namespace {

bool isContractFunction(Function *F) {
  auto name = F->getName();
  return name == Naming::CONTRACT_REQUIRES ||
         name == Naming::CONTRACT_ENSURES || name == Naming::CONTRACT_INVARIANT;
}

typedef std::vector<BasicBlock *> BlockList;
typedef std::map<const Loop *, BlockList> LoopMap;

// Return the list of blocks which dominate the given blocks in the given
// function.
// NOTE this procedure assumes blocks are ordered in dominated order, both
// in the given selection of blocks, as well as in the given function.
BlockList blockPrefix(BlockList BBs, Function &F) {
  BlockList prefix;
  if (!BBs.empty()) {
    for (auto &BB : F) {
      prefix.push_back(&BB);
      if (&BB == BBs.back())
        break;
    }
  }
  return prefix;
}

// Return the list of blocks which dominate the given blocks in the given
// loop, not including the loop head.
// NOTE this procedure assumes blocks are ordered in dominated order, both
// in the given selection of blocks, as well as in the given loop.
BlockList blockPrefix(BlockList BBs, const Loop &L) {
  BlockList prefix;
  if (!BBs.empty()) {
    for (auto BB : L.getBlocks()) {
      if (BB == L.getHeader())
        continue;
      prefix.push_back(BB);
      if (BB == BBs.back())
        break;
    }
  }
  return prefix;
}

// Split the basic blocks of the given function such that each invocation to
// contract functions is the last non-terminator instruction in its block.
std::tuple<BlockList, LoopMap> splitContractBlocks(Function &F, LoopInfo &LI) {

  BlockList contractBlocks;
  LoopMap invariantBlocks;

  std::deque<BasicBlock *> blocks;
  for (auto &BB : F)
    blocks.push_back(&BB);

  while (!blocks.empty()) {
    auto BB = blocks.front();
    blocks.pop_front();

    for (auto &I : *BB) {
      if (auto CI = dyn_cast<CallInst>(&I)) {
        if (auto *CF = CI->getCalledFunction()) {
          if (isContractFunction(CF)) {
            SDEBUG(errs() << "splitting block at contract invocation: " << *CI
                          << "\n");
            BasicBlock *B = CI->getParent();
            auto NewBB = B->splitBasicBlock(++CI->getIterator());
            auto L = LI.getLoopFor(B);
            if (L)
              L->addBasicBlockToLoop(NewBB, LI);
            blocks.push_front(NewBB);

            if (L)
              invariantBlocks[L].push_back(B);
            else
              contractBlocks.push_back(B);

            break;
          }
        }
      }
    }
  }

  contractBlocks = blockPrefix(contractBlocks, F);

  for (auto const &entry : invariantBlocks) {
    auto L = entry.first;
    auto BBs = entry.second;
    invariantBlocks[L] = blockPrefix(BBs, *L);
  }

  return std::make_tuple(contractBlocks, invariantBlocks);
}

// Return the list of contract invocations in the given function.
std::vector<CallInst *> getContractInvocations(Function &F) {
  std::vector<CallInst *> CIs;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto CI = dyn_cast<CallInst>(&I))
        if (auto F = CI->getCalledFunction())
          if (isContractFunction(F))
            CIs.push_back(CI);
  return CIs;
}

// Replace the given invocation with a return of its argument; also remove
// all other contract invocations.
void setReturnToArgumentValue(Function *F, CallInst *II) {

  for (auto &BB : *F) {

    // Replace existing returns with return true.
    if (auto RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
      IRBuilder<> Builder(RI);
      Builder.CreateRet(
          ConstantInt::getTrue(F->getFunctionType()->getReturnType()));
      RI->eraseFromParent();
      continue;
    }

    // Erase contract invocations, and replace the given invocation
    // with a return of its argument.
    for (auto &I : BB) {
      if (auto CI = dyn_cast<CallInst>(&I)) {
        if (auto F = CI->getCalledFunction()) {
          if (isContractFunction(F)) {
            if (CI == II) {
              IRBuilder<> Builder(CI);
              BB.getTerminator()->eraseFromParent();
              Builder.CreateRet(CI->getArgOperand(0));
            }
            CI->eraseFromParent();
            break;
          }
        }
      }
    }
  }
}

// Return a copy of the given function in which the given invocation is
// replaced by a return of its argument value, and all contract
// invocations are removed.
Function *getContractExpr(Function *F, CallInst *I) {
  ValueToValueMapTy VMap;
  SmallVector<ReturnInst *, 8> Returns;

  FunctionType *FT = FunctionType::get(I->getFunctionType()->getParamType(0),
                                       F->getFunctionType()->params(),
                                       F->getFunctionType()->isVarArg());

  Function *NewF = Function::Create(FT, F->getLinkage(), Naming::CONTRACT_EXPR,
                                    F->getParent());

  // Loop over the arguments, copying the names of the mapped arguments over...
  // See implementation of llvm::CloneFunction
  Function::arg_iterator DestA = NewF->arg_begin();
  for (auto &A : F->args()) {
    DestA->setName(A.getName());
    VMap[&A] = &*DestA++;
  }
  CloneFunctionInto(NewF, F, VMap, false, Returns);
  setReturnToArgumentValue(NewF, dyn_cast<CallInst>(VMap[I]));
  return NewF;
}

// Return copies of the given function in for each contract invocation, in
// which each returns the argument value of the corresponding contract
// invocation. The first function of each returned pair is the invoked
// contract function; the second function is the new function created for the
// given invocation.
std::vector<std::tuple<Function *, Function *>> getContractExprs(Function &F) {
  std::vector<std::tuple<Function *, Function *>> Fs;
  for (auto CI : getContractInvocations(F)) {
    Function *newF = getContractExpr(&F, CI);
    Fs.push_back(std::make_tuple(CI->getCalledFunction(), newF));
  }
  return Fs;
}
} // namespace

bool ExtractContracts::runOnModule(Module &M) {
  bool modified = false;

  std::vector<Function *> Fs;
  std::vector<Function *> newFs;

  for (Function &F : M)
    if (!F.isDeclaration())
      Fs.push_back(&F);

  for (auto F : Fs) {
    BlockList contractBlocks;
    LoopMap invariantBlocks;
    auto &LI = getAnalysis<LoopInfoWrapperPass>(*F).getLoopInfo();
    std::tie(contractBlocks, invariantBlocks) = splitContractBlocks(*F, LI);

    if (!contractBlocks.empty() || !invariantBlocks.empty()) {
      SDEBUG(errs() << "function " << F->getName() << " after splitting: " << *F
                    << "\n");
      modified = true;
    }

    if (!contractBlocks.empty()) {
      auto *newF = CodeExtractor(contractBlocks)
                       .extractCodeRegion(CodeExtractorAnalysisCache(*F));

      std::vector<CallInst *> Is;
      for (auto V : newF->users())
        if (auto I = dyn_cast<CallInst>(V))
          Is.push_back(I);

      for (auto I : Is) {
        IRBuilder<> Builder(I);

        // insert one contract invocation per invocation in the original
        // function
        for (auto Fs : getContractExprs(*newF)) {
          std::vector<Value *> Args;
          for (auto &A : I->arg_operands())
            Args.push_back(A);
          auto *E = Builder.CreateCall(std::get<1>(Fs), Args);
          Builder.CreateCall(std::get<0>(Fs), {E});
          newFs.push_back(std::get<1>(Fs));
        }
        I->eraseFromParent();
      }
      newF->eraseFromParent();
      SDEBUG(errs() << "function " << F->getName()
                    << " after contract extraction: " << *F << "\n");
    }

    for (auto const &entry : invariantBlocks) {
      auto BBs = entry.second;
      auto *newF =
          CodeExtractor(BBs).extractCodeRegion(CodeExtractorAnalysisCache(*F));

      std::vector<CallInst *> Is;
      for (auto V : newF->users())
        if (auto I = dyn_cast<CallInst>(V))
          Is.push_back(I);

      for (auto I : Is) {
        IRBuilder<> Builder(I);

        // insert one invariant invocation per invocation in the original loop
        for (auto Fs : getContractExprs(*newF)) {
          std::vector<Value *> Args;
          for (auto &A : I->arg_operands())
            Args.push_back(A);
          auto *E = Builder.CreateCall(std::get<1>(Fs), Args);
          Builder.CreateCall(std::get<0>(Fs), {E});
          newFs.push_back(std::get<1>(Fs));
        }
        I->eraseFromParent();
      }
      newF->eraseFromParent();
      SDEBUG(errs() << "function " << F->getName()
                    << " after invariant extraction: " << *F << "\n");
    }
  }

  for (auto F : newFs) {
    SDEBUG(errs() << "added function:" << *F);
  }

  return modified;
}

void ExtractContracts::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<DominatorTreeWrapperPass>();
}

// Pass ID variable
char ExtractContracts::ID = 0;

// Register the pass
static RegisterPass<ExtractContracts> X("extract-contracts",
                                        "Extract Contracts");
} // namespace smack
