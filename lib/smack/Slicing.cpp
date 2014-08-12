//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/Slicing.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include <vector>
#include <queue>
#include <set>

using namespace std;

namespace llvm {

  typedef SmallVector< pair<const BasicBlock*, const BasicBlock*>, 10 > EdgeList;

  bool contains(EdgeList& backedges, const BasicBlock* src, const BasicBlock* tgt) {
    for (EdgeList::iterator E = backedges.begin(), End = backedges.end(); E != End; ++E) {
      if (E->first == src && E->second == tgt)
        return true;
    }
    return false;
  }

  unordered_set<Value*> getSlice(Value* V) {
    unordered_set<Value*> slice;
    Instruction* I = dyn_cast<Instruction>(V);
    assert(I && "Expected instruction value.");

    const BasicBlock* B = I->getParent();
    const Function* F = B->getParent();
    EdgeList backedges;
    FindFunctionBackedges(*F,backedges);

    queue<Instruction*> workList;
    workList.push(I);

    while (!workList.empty()) {
      Instruction* I = workList.front();
      workList.pop();
      if (slice.count(I))
        continue;
      slice.insert(I);
      slice.insert(I->getParent());

      // ENSURE EACH BLOCK HAS A TERMINATOR
      if (BranchInst* Br = dyn_cast<BranchInst>(I->getParent()->getTerminator()))
        if (I->getParent() != B)
          workList.push(Br);

      if (BranchInst* Br = dyn_cast<BranchInst>(I)) {
        if (Br->isConditional()) {
          if (Instruction* J = dyn_cast<Instruction>(Br->getCondition())) {
            workList.push(J);
          }
          slice.insert(Br->getSuccessor(1));
        }
        slice.insert(Br->getSuccessor(0));
        continue;
      }

      if (PHINode* Phi = dyn_cast<PHINode>(I)) {
        for (PHINode::block_iterator B = Phi->block_begin(); B != Phi->block_end(); ++B) {
          if (contains(backedges,*B,I->getParent())) {
            goto NEXT;
          }
        }

        for (PHINode::block_iterator B = Phi->block_begin(); B != Phi->block_end(); ++B) {
          workList.push( (*B)->getTerminator() );
        }
      }

      for (User::op_iterator U = I->op_begin(); U != I->op_end(); ++U) {
        if (Instruction* J = dyn_cast<Instruction>(U)) {
          if (!contains(backedges,J->getParent(),I->getParent())) {
            workList.push(J);
          }
        }
      }

NEXT: ; // no-op
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
        if (Br->isConditional()) {
          if (Instruction* J = dyn_cast<Instruction>(Br->getCondition()))
            workList.push(J);
        } else {
          // TODO FIGURE THIS OUT & CLEAN IT UP
          succ.insert(make_pair(Br->getParent(),Br->getSuccessor(0)));
        }
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
        // TODO FIGURE THIS OUT & CLEAN IT UP
        if (BasicBlock* C = succ[B]) {
          // assert(C && "Successor not found!");
          B->replaceAllUsesWith(C);
          B->eraseFromParent();
        }
      }
    }
  }

}
