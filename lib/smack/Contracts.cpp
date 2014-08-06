#include "smack/Contracts.h"
#include "llvm/Support/InstIterator.h"

namespace smack {
  using namespace llvm;

Expr* ContractsExtractor::sliceExpr(Value* V) {
  Instruction* I = dyn_cast<Instruction>(V);
  assert(I && "Expected instruction.");
  Function* F = I->getParent()->getParent();
  CodeExpr* code = new CodeExpr(rep.getProgram());
  SmackInstGenerator igen(rep, *code, naming, exprs);
  naming.enter();
  igen.visitSlice(F,I);
  naming.leave();
  removeSlice(I);
  return code;
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
    Value* arg = ci.getArgOperand(0);
    Value* idx = expressionIdx(ci.getContext());
    ci.setArgOperand(0,idx);
    const Expr* e = sliceExpr(arg);
    exprs.push_back(e);

    BasicBlock* body = ci.getParent();
    BasicBlock* head = body->getSinglePredecessor();
    assert(head && "Expected single predecessor block.");
    ArrayRef<Value*> args(idx);
    ArrayRef<Type*> params(Type::getInt32Ty(ci.getContext()));
    CallInst::Create(
      Function::Create(
        FunctionType::get(Type::getVoidTy(ci.getContext()),params,false),
        GlobalValue::ExternalLinkage, "iassume"),
      args,"",head->getTerminator());
    unsigned count = 0;
    for (pred_iterator B = pred_begin(head), E = pred_end(head); B != E; ++B) {
      CallInst::Create(
        Function::Create(
          FunctionType::get(Type::getVoidTy(ci.getContext()),params,false),
          GlobalValue::ExternalLinkage, "iassert"),
        args,"",(*B)->getTerminator());
      count++;
    }
    assert(count == 2 && "Expected head with two predecessors.");
    count = 0;
    for (succ_iterator B = succ_begin(head), E = succ_end(head); B != E; ++B) {
      count++;
    }
    assert(count == 2 && "Expected head with two successors.");
    ci.eraseFromParent();
  }
}

}
