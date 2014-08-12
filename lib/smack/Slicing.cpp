//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/Slicing.h"
#include "smack/SmackInstGenerator.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include <vector>
#include <queue>
#include <set>

using namespace std;
using namespace llvm;

namespace smack {

typedef SmallVector< pair<const BasicBlock*, const BasicBlock*>, 10 > EdgeList;

bool contains(EdgeList& backedges, const BasicBlock* src, const BasicBlock* tgt) {
  for (EdgeList::iterator E = backedges.begin(), End = backedges.end(); E != End; ++E) {
    if (E->first == src && E->second == tgt)
      return true;
  }
  return false;
}

Slice::Slice(string name, Instruction& I)
  : name(name), value(I), block(*I.getParent()),
    function(*block.getParent()), context(function.getContext()) {

  EdgeList backedges;
  FindFunctionBackedges(function,backedges);

  queue<Instruction*> workList;
  workList.push(&I);

  while (!workList.empty()) {
    Instruction* I = workList.front();
    workList.pop();
    if (values.count(I))
      continue;
    values.insert(I);
    values.insert(I->getParent());

    // ENSURE EACH BLOCK HAS A TERMINATOR
    if (BranchInst* Br = dyn_cast<BranchInst>(I->getParent()->getTerminator()))
      if (I->getParent() != &block)
        workList.push(Br);

    if (BranchInst* Br = dyn_cast<BranchInst>(I)) {
      if (Br->isConditional()) {
        if (Instruction* J = dyn_cast<Instruction>(Br->getCondition())) {
          workList.push(J);
        }
        values.insert(Br->getSuccessor(1));
      }
      values.insert(Br->getSuccessor(0));
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

}

void Slice::remove() {
  Instruction* I = dyn_cast<Instruction>(&value);
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

string Slice::getName() {
  return name;
}

const Decl* Slice::getBoogieDecl(Naming& naming, SmackRep& rep, ExpressionList& exprs) {
  vector< pair<string,string> > params;
  for (unordered_set<Value*>::iterator V = inputs.begin(), E = inputs.end(); V != E; ++V)
    params.push_back(make_pair(naming.get(**V), rep.type(*V)));

  CodeExpr* code = new CodeExpr(rep.getProgram());
  SmackInstGenerator igen(rep, *code, naming, exprs);
  naming.enter();

  // igen.visitSlice(function,value);

  for (Function::iterator B = function.begin(), E = function.end(); B != E; ++B) {
    if (!values.count(B))
      continue;
    igen.visitBasicBlock(*B);

    for (BasicBlock::iterator I = B->begin(), G = B->end(); I != G; ++I) {
      if (!values.count(&*I))
        continue;
      igen.visit(*I);
    }

    if (B == block) {
      // emit(Stmt::return_(rep.expr(I)));
      Instruction* I = ReturnInst::Create(context,&value);
      igen.visit(I);
      delete I;

    } else if (!values.count(B->getTerminator())) {
      // emit(Stmt::assume(Expr::lit(false)));
      // emit(Stmt::goto_(getBlock(I->getParent())->getName()));
      igen.visit(new UnreachableInst(context));
      Instruction* I = ReturnInst::Create(context,ConstantInt::getTrue(context));
      igen.visit(I);
      delete I;
    }
  }

  naming.leave();

  Decl* D = Decl::function(getName(),params,"bool",code);
  D->addAttr(Attr::attr("inline"));
  return D;
}

const Expr* Slice::getBoogieExpression(Naming& naming) {
  vector<const Expr*> args;
  for (unordered_set<Value*>::iterator V = inputs.begin(), E = inputs.end(); V != E; ++V)
    args.push_back(Expr::id(naming.get(**V)));
  return Expr::fn(getName(),args);
}

}
