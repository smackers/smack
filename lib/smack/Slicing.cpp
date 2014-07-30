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
    assert( I && "Expected instruction value.");

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
    }

    return slice;
  }

  Function* slice(Value* V) {
    map<BasicBlock*, BasicBlock*> blockMap;

    Instruction* I = dyn_cast<Instruction>(V);
    assert(I && "Expected instruction value.");
    Function* F = I->getParent()->getParent();
    Function* slice = Function::Create(F->getFunctionType(), GlobalValue::ExternalLinkage);

    queue<Instruction*> workList;
    set<Instruction*> covered;

    DEBUG(errs() << "COMPUTING SLICE " << *V << "\n");
    DEBUG(errs() << "FROM " << *F << "\n");

    BasicBlock* B = BasicBlock::Create(slice->getContext(), "", slice, 0);
    blockMap.insert(make_pair(I->getParent(),B));
    ReturnInst::Create(slice->getContext(),I,B);
    workList.push(I);

    while (!workList.empty()) {
      Instruction* I = workList.front();
      workList.pop();
      if (covered.count(I))
        continue;
      covered.insert(I);

      BasicBlock* B = I->getParent();
      I->removeFromParent();

      // TODO REMOVE THE BLOCK?
      // TODO REMOVE TERMINATORS?

      BasicBlock* C;
      if (blockMap.count(B))
        C = blockMap.find(B)->second;
      else
        blockMap.insert(make_pair(B,
          C = BasicBlock::Create(slice->getContext(), "", slice, 0)));
      C->getInstList().push_front(I);

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
    }

    DEBUG(errs() << "COMPUTED SLICE " << *slice << "\n");
    DEBUG(errs() << "WITH LEFTOVER " << *F << "\n");

    return slice;
  }

}
