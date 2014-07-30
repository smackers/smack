#include "smack/Contracts.h"
#include "llvm/Support/InstIterator.h"

namespace smack {
  using namespace llvm;

Expr* ContractsExtractor::sliceExpr(Value* V) {
  Instruction* I = dyn_cast<Instruction>(V);
  assert(I && "Expected instruction.");
  Function* F = I->getParent()->getParent();
  Instruction* J = ReturnInst::Create(I->getContext(), I, I->getParent());

  CodeExpr* code = new CodeExpr(*rep.getProgram());
  SmackInstGenerator igen(rep, *code, extracted.size());
  igen.setExtracted(extracted);
  igen.visitSlice(F,getSlice(J));
  delete llvm::slice(J);
  return code;
}

void ContractsExtractor::visitCallInst(CallInst& ci) {
  Function* f = ci.getCalledFunction();

  if (f && rep.id(f).find("forall") != string::npos) {
    assert(ci.getNumArgOperands() == 2 && "Unexpected operands to forall.");
    Value* var = ci.getArgOperand(0);
    Value* arg = ci.getArgOperand(1);
    const Expr* e = Expr::forall(rep.getString(var), "int", sliceExpr(arg));
    ci.setArgOperand(1,extractionIdx(ci.getContext()));
    extracted.push_back(e);

  } else if (f && rep.id(f).find("exists") != string::npos) {
    assert(ci.getNumArgOperands() == 2 && "Unexpected operands to exists.");
    Value* var = ci.getArgOperand(0);
    Value* arg = ci.getArgOperand(1);
    const Expr* e = Expr::exists(rep.getString(var), "int", sliceExpr(arg));
    ci.setArgOperand(1,extractionIdx(ci.getContext()));
    extracted.push_back(e);

  } else if (f && rep.id(f).find("requires") != string::npos) {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to requires.");
    Value* V = ci.getArgOperand(0);
    ci.setArgOperand(0,ConstantInt::getTrue(ci.getContext()));
    proc.addRequires(sliceExpr(V));
    ci.eraseFromParent();

  } else if (f && rep.id(f).find("ensures") != string::npos) {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to ensures.");
    Value* V = ci.getArgOperand(0);
    ci.setArgOperand(0,ConstantInt::getTrue(ci.getContext()));
    proc.addEnsures(sliceExpr(V));
    ci.eraseFromParent();

  } else if (f && rep.id(f).find("invariant") != string::npos) {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to invariant.");
    Value* arg = ci.getArgOperand(0);
    Value* idx = extractionIdx(ci.getContext());
    ci.setArgOperand(0,idx);
    const Expr* e = sliceExpr(arg);
    extracted.push_back(e);

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
