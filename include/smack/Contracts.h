#include "llvm/InstVisitor.h"
#include "llvm/Support/CFG.h"
#include "smack/Slicing.h"
#include "smack/SmackRep.h"
#include "smack/SmackInstGenerator.h"
#include "smack/BoogieAst.h"

namespace smack {
using namespace llvm;

class ContractsExtractor : public InstVisitor<ContractsExtractor> {
private:
  SmackRep& rep;
  ProcDecl& proc;
  Naming& naming;
  ExpressionList& exprs;

public:
  ContractsExtractor(SmackRep& R, ProcDecl& P, Naming& N, ExpressionList& E)
    : rep(R), proc(P), naming(N), exprs(E) {}

  void visitCallInst(CallInst& ci);

private:
  Expr* sliceExpr(Value* v);

  Value* expressionIdx(LLVMContext& ctx) {
    return ConstantInt::get(Type::getInt32Ty(ctx),exprs.size());
  }
};

}
