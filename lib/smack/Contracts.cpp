#include "smack/Contracts.h"

namespace smack {

Expr* ContractsExtractor::sliceExpr(llvm::Value* v) {
  CodeExpr* code = new CodeExpr(*rep.getProgram());
  SmackInstGenerator igen(rep, *code, slices.size());
  llvm::Function* sliced = llvm::get_slice(v);
  igen.setSliceMap(&slices);
  igen.visit(sliced);
  delete sliced;
  return code;
}

void ContractsExtractor::visitCallInst(llvm::CallInst& ci) {
  using namespace llvm;
  Function* f = ci.getCalledFunction();

  if (f && rep.id(f).find("forall") != string::npos) {
    assert(ci.getNumArgOperands() == 2 && "Unexpected operands to forall.");
    Value* var = ci.getArgOperand(0);
    Value* arg = ci.getArgOperand(1);
    const Expr* e = Expr::forall(rep.getString(var), "int", sliceExpr(arg));
    ci.setArgOperand(1,ConstantInt::get(Type::getInt32Ty(ci.getContext()),slices.size()));
    slices.push_back(e);
    llvm::remove_slice(arg);

  } else if (f && rep.id(f).find("exists") != string::npos) {
    assert(ci.getNumArgOperands() == 2 && "Unexpected operands to exists.");
    Value* var = ci.getArgOperand(0);
    Value* arg = ci.getArgOperand(1);
    const Expr* e = Expr::exists(rep.getString(var), "int", sliceExpr(arg));
    ci.setArgOperand(1,ConstantInt::get(Type::getInt32Ty(ci.getContext()),slices.size()));
    slices.push_back(e);
    llvm::remove_slice(arg);

  } else if (f && rep.id(f).find("requires") != string::npos) {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to requires.");
    proc.addRequires(sliceExpr(ci.getArgOperand(0)));
    llvm::remove_slice(&ci);

  } else if (f && rep.id(f).find("ensures") != string::npos) {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to ensures.");
    proc.addEnsures(sliceExpr(ci.getArgOperand(0)));
    llvm::remove_slice(&ci);

  } else if (f && rep.id(f).find("invariant") != string::npos) {
    assert(ci.getNumArgOperands() == 1 && "Unexpected operands to invariant.");
    Value* arg = ci.getArgOperand(0);
    const Expr* e = sliceExpr(arg);
    Value* sliceIdx = ConstantInt::get(Type::getInt32Ty(ci.getContext()),slices.size());
    ci.setArgOperand(0,sliceIdx);
    slices.push_back(e);

    BasicBlock* body = ci.getParent();
    BasicBlock* head = body->getSinglePredecessor();
    assert(head && "Expected single predecessor block.");
    ArrayRef<Value*> args(sliceIdx);
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

    llvm::remove_slice(&ci);
  }
}

}
