//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/Slicing.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include <vector>
#include <queue>
#include <set>

using namespace std;

namespace llvm {

  unordered_set<Instruction*> getSlice(Value* V) {
    unordered_set<Instruction*> slice;
    Instruction* I = dyn_cast<Instruction>(V);
    assert(I && "Expected instruction value.");

    queue<Instruction*> workList;
    workList.push(I);

    while (!workList.empty()) {
      Instruction* I = workList.front();
      workList.pop();
      if (slice.count(I))
        continue;
      slice.insert(I);

      if (BranchInst* Br = dyn_cast<BranchInst>(I)) {
        if (Br->isConditional()) {
          if (Instruction* J = dyn_cast<Instruction>(Br->getCondition())) {
            workList.push(J);
          }
        }
      } else {
        for (User::op_iterator U = I->op_begin(); U != I->op_end(); ++U) {
          if (Instruction* J = dyn_cast<Instruction>(U)) {
            workList.push(J);
          }
        }
      }

      if (PHINode* Phi = dyn_cast<PHINode>(I)) {
        for (PHINode::block_iterator B = Phi->block_begin(); B != Phi->block_end(); ++B) {
          workList.push( (*B)->getTerminator() );
        }
      }

      // ENSURE EACH BLOCK HAS A TERMINATOR
      if (BranchInst* Br = dyn_cast<BranchInst>(I->getParent()->getTerminator()))
        workList.push(Br);
    }

    return slice;
  }

  void removeSlice(Value* V) {

    Instruction* I = dyn_cast<Instruction>(V);
    assert(I && "Expected instruction value.");

    queue<Instruction*> workList;
    set<Instruction*> covered;
    map<BasicBlock*,BasicBlock*> succ;

    workList.push(I);

    while (!workList.empty()) {
      Instruction* I = workList.front();
      workList.pop();
      if (covered.count(I))
        continue;

      covered.insert(I);

      if (I->getNumUses() > 1)
        continue;

      if (BranchInst* Br = dyn_cast<BranchInst>(I)) {
        succ.insert(make_pair(Br->getParent(),Br->getSuccessor(0)));
        if (Br->isConditional())
          if (Instruction* J = dyn_cast<Instruction>(Br->getCondition()))
            workList.push(J);
      } else {
        for (User::op_iterator U = I->op_begin(); U != I->op_end(); ++U)
          if (Instruction* J = dyn_cast<Instruction>(U))
            workList.push(J);
      }

      if (PHINode* Phi = dyn_cast<PHINode>(I)) {
        for (PHINode::block_iterator A = Phi->block_begin(); A != Phi->block_end(); ++A) {
          workList.push( (*A)->getTerminator() );
        }
      }

      BasicBlock* B = I->getParent();
      I->eraseFromParent();

      if (B->getInstList().size() == 0) {
        BasicBlock* C = succ[B];
        assert(C && "Successor not found!");
        B->replaceAllUsesWith(C);
        B->eraseFromParent();
      }
    }
  }

}
