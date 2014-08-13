#include "smack/Contracts.h"
#include "llvm/Support/InstIterator.h"

using namespace llvm;

namespace smack {

unsigned ContractsExtractor::uniqueSliceId = 0;

const Expr* ContractsExtractor::sliceExpr(Value* V) {
  Instruction* I = dyn_cast<Instruction>(V);
  assert(I && "Expected instruction.");

  stringstream name;
  name << "$expr" << uniqueSliceId++;
  Slice S(name.str(),*I);
  rep.getProgram().addDecl((Decl*) S.getBoogieDecl(naming,rep,exprs));
  S.remove();
  return S.getBoogieExpression(naming,rep);
}

void ContractsExtractor::visitCallInst(CallInst& ci) {
  Function* f = ci.getCalledFunction();

  if (f && naming.get(*f).find("forall") != string::npos) {
    assert(ci.getNumArgOperands() == 2 && "Unexpected operands to forall.");
    Value* var = ci.getArgOperand(0);
    Value* arg = ci.getArgOperand(1);
    ci.setArgOperand(1,expressionIdx(ci.getContext()));
    const Expr* e = Expr::forall(rep.getString(var), "int", sliceExpr(arg));
    exprs.push_back(e);

  } else if (f && naming.get(*f).find("exists") != string::npos) {
    assert(ci.getNumArgOperands() == 2 && "Unexpected operands to exists.");
    Value* var = ci.getArgOperand(0);
    Value* arg = ci.getArgOperand(1);
    ci.setArgOperand(1,expressionIdx(ci.getContext()));
    const Expr* e = Expr::exists(rep.getString(var), "int", sliceExpr(arg));
    exprs.push_back(e);

  } else if (f && naming.get(*f).find("requires") != string::npos) {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to requires.");
    Value* V = ci.getArgOperand(0);
    ci.setArgOperand(0,ConstantInt::getTrue(ci.getContext()));
    proc.addRequires(sliceExpr(V));
    ci.eraseFromParent();

  } else if (f && naming.get(*f).find("ensures") != string::npos) {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to ensures.");
    Value* V = ci.getArgOperand(0);
    ci.setArgOperand(0,ConstantInt::getTrue(ci.getContext()));
    proc.addEnsures(sliceExpr(V));
    ci.eraseFromParent();

  } else if (f && naming.get(*f).find("invariant") != string::npos) {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to invariant.");
    Value* V = ci.getArgOperand(0);
    Value* idx = expressionIdx(ci.getContext());
    ci.setArgOperand(0,idx);
    exprs.push_back(sliceExpr(V));

    BasicBlock* body = ci.getParent();
    BasicBlock* head = body->getSinglePredecessor();
    assert(head && "Expected single predecessor block.");

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
