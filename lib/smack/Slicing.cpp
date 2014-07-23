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

  Function* slice(Function* f, Value* v, bool keep=false) {
    ValueToValueMapTy VMap;
    Function* slice = CloneFunction(f,VMap,true);
    v = VMap[v];

    set<Instruction*> markedI;
    set<BasicBlock*> markedB;
    queue<Instruction*> workList;

    if (Instruction* I = dyn_cast<Instruction>(v)) {
      workList.push(I);
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
        if (markedI.count(I) == 0)
          goneI.push_back(I);
      if (markedB.count(B) == 0)
        goneB.push_back(B);
    }
    
    // TODO ERASE FROM THE ORIGINAL COPY
    // for (Function::iterator B = f->begin(); B != f->end(); ++B) {
    //   for (BasicBlock::iterator I = B->begin(); I != B->end(); ++I) {
    //     Value* V = VMap[I];
    //     if (Instruction* J = dyn_cast<Instruction>(V)) {
    //       if (markedI.count(J) > 0) {
    //         goneI.push_back(I);
    //       }
    //     }
    //   }
    // }
    
    for (vector<Instruction*>::iterator I = goneI.begin(); I != goneI.end(); ++I)
      (*I)->eraseFromParent();

    for (vector<BasicBlock*>::iterator B = goneB.begin(); B != goneB.end(); ++B)
      (*B)->eraseFromParent();    

    return slice;
  }

}

namespace smack {
  
  Expr* slice(SmackRep& rep, llvm::Value* v, bool keep=false) {
    CodeExpr* code = new CodeExpr(*rep.getProgram());
    SmackInstGenerator igen(rep, *code);
    if (llvm::Instruction* I = llvm::dyn_cast<llvm::Instruction>(v)) {
      llvm::Function* sliced = llvm::slice(I->getParent()->getParent(),v,keep);
      igen.visit(sliced);
      delete sliced;
    }
    return code;
  }
}
