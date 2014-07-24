//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/Instructions.h"
#include "smack/BoogieAst.h"
#include "smack/SmackRep.h"
#include "smack/SmackInstGenerator.h"
#include <vector>
#include <queue>
#include <set>

using namespace std;

namespace llvm {

  Function* slice(Value* v, bool exclude=false, bool inPlace=false) {
    Function* slice;

    queue<Instruction*> workList;
    set<Instruction*> markedI;
    set<BasicBlock*> markedB;

    Instruction* I = dyn_cast<Instruction>(v);
    assert(I && "Expected instruction value.");

    Function* f = I->getParent()->getParent();

    // DEBUG(llvm::errs() << "COMPUTING SLICE " << *v << "\n");
    // DEBUG(llvm::errs() << "IN " << *f << "\n");
    // DEBUG(llvm::errs() << "exclude? " << exclude << "\n");
    // DEBUG(llvm::errs() << "inPlace? " << inPlace << "\n");

    if (inPlace) {
      slice = f;
    } else {
      ValueToValueMapTy VMap;
      slice = CloneFunction(f,VMap,true);
      v = VMap[v];
    }

    I = dyn_cast<Instruction>(v);
    assert(I && "Expected instruction value.");

    if (exclude) {
      workList.push(I);
    } else {
      I->getParent()->getTerminator()->eraseFromParent();
      workList.push( ReturnInst::Create(I->getContext(),I,I->getParent()) );
    }

    while (!workList.empty()) {
      Instruction* I = workList.front();
      workList.pop();

      markedI.insert(I);
      markedB.insert(I->getParent());      

      if (PHINode* Phi = dyn_cast<PHINode>(I)) {
        for (PHINode::block_iterator B = Phi->block_begin(); B != Phi->block_end(); ++B) {
          workList.push( (*B)->getTerminator() );
        }
      }

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
    }

    vector<Instruction*> goneI;
    vector<BasicBlock*> goneB;

    for (Function::iterator B = slice->begin(); B != slice->end(); ++B) {
      for (BasicBlock::iterator I = B->begin(); I != B->end(); ++I)
        if (!markedI.count(I) == !exclude) {
          goneI.push_back(I);
          I->dropAllReferences();
        }

      if (!exclude && markedB.count(B) == 0)
        goneB.push_back(B);
    }

    for (vector<Instruction*>::reverse_iterator I = goneI.rbegin(); I != goneI.rend(); ++I) {
      BasicBlock* B = (*I)->getParent();
      // NOTE THIS WILL BREAK SINCE I'S REFERENCES HAVE BEEN DROPPED
      // DEBUG(errs() << "ERASING " << **I << "\n");
      // DEBUG(errs() << "FROM " << *(*I)->getParent() << "\n");
      // DEBUG(errs() << "IN " << *(*I)->getParent()->getParent() << "\n");
      (*I)->eraseFromParent();
      if (exclude && B->empty())
        goneB.push_back(B);
    }

    for (vector<BasicBlock*>::iterator B = goneB.begin(); B != goneB.end(); ++B) {
      // DEBUG(errs() << "ERASING " << **B << "\n");
      // DEBUG(errs() << "FROM " << *(*B)->getParent() << "\n");
      (*B)->eraseFromParent();
    }

    // DEBUG(llvm::errs() << "COMPUTED SLICE " << *slice << "\n");

    return slice;
  }

  Function* get_slice(Value* v) {
    return slice(v);
  }

  void remove_slice(Value* v) {
    slice(v,true,true);
  }

}
