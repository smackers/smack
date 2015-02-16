//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "smack/Contracts.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/CFG.h"

using namespace llvm;

namespace smack {

unsigned ContractsExtractor::uniqueSliceId = 0;

Slice* ContractsExtractor::extractSlice(Value* V) {
  Instruction* I = dyn_cast<Instruction>(V);
  assert(I && "Expected instruction.");

  stringstream name;
  name << "$expr" << uniqueSliceId++;
  Slice* S = new Slice(*I, slices, name.str());
  if (Decl* D = (Decl*) S->getBoogieDecl(naming,rep))
    rep.getProgram().addDecl(D);
  S->remove();
  return S;
}

typedef SmallVector< pair<const BasicBlock*, const BasicBlock*>, 10 > EdgeList;

bool looksLikeLoopHead(BasicBlock* B) {
  EdgeList backedges;
  FindFunctionBackedges(*B->getParent(), backedges);
  for (pred_iterator A = pred_begin(B), Z = pred_end(B); A != Z; ++A)
    for (EdgeList::iterator E = backedges.begin(), End = backedges.end(); E != End; ++E)
      if (E->first == *A && E->second == B)
        return true;
  return false;
}

void ContractsExtractor::visitCallInst(CallInst& ci) {
  Function* f = ci.getCalledFunction();
  string name = f && f->hasName() ? f->getName().str() : "";

  if (name == "forall") {
    assert(ci.getNumArgOperands() == 2 && "Unexpected operands to forall.");
    Value* arg = ci.getArgOperand(1);
    ci.setArgOperand(1,sliceIdx(ci.getContext()));
    slices.push_back(extractSlice(arg));

  } else if (name == "exists") {
    assert(ci.getNumArgOperands() == 2 && "Unexpected operands to exists.");
    Value* arg = ci.getArgOperand(1);
    ci.setArgOperand(1,sliceIdx(ci.getContext()));
    slices.push_back(extractSlice(arg));

  } else if (name == "requires") {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to requires.");
    Value* V = ci.getArgOperand(0);
    ci.setArgOperand(0,ConstantInt::getTrue(ci.getContext()));
    proc.addRequires(extractSlice(V)->getBoogieExpression(naming,rep));
    ci.eraseFromParent();

  } else if (name == "ensures") {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to ensures.");
    Value* V = ci.getArgOperand(0);
    ci.setArgOperand(0,ConstantInt::getTrue(ci.getContext()));
    proc.addEnsures(extractSlice(V)->getBoogieExpression(naming,rep));
    ci.eraseFromParent();

  } else if (name == "invariant") {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to invariant.");

    BasicBlock* body = ci.getParent();
    BasicBlock* head = body;
    do {
      pred_iterator P = pred_begin(head);
      assert(P != pred_end(head) && "Expected predecessors!");
      head = *P;
    } while (!looksLikeLoopHead(head));

    Value* V = ci.getArgOperand(0);
    ci.setArgOperand(0,sliceIdx(ci.getContext()));
    slices.push_back(extractSlice(V));
    ci.removeFromParent();

    // NOTE Boogie only considers only assertions at the beginning of the loop
    // head block to be loop invariants. Therefore we push this instruction to
    // the front -- just after any Phi nodes.
    BasicBlock::iterator I = head->begin();
    while (isa<PHINode>(I)) ++I;
    head->getInstList().insert(I,&ci);
  }
}

}
