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
  
  vector<const Expr*> extracted;

public:
  ContractsExtractor(SmackRep& r, ProcDecl& d) : rep(r), proc(d) {}

  vector<const Expr*>& getExtracted() { return extracted; }

  void visitCallInst(CallInst& ci);

private:
  Expr* sliceExpr(Value* v);

  Value* extractionIdx(LLVMContext& ctx) {
    return ConstantInt::get(Type::getInt32Ty(ctx),extracted.size());
  }
};

}
