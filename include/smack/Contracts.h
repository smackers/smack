#include "llvm/InstVisitor.h"
#include "llvm/Support/CFG.h"
#include "smack/Slicing.h"
#include "smack/SmackRep.h"
#include "smack/SmackInstGenerator.h"
#include "smack/BoogieAst.h"

namespace smack {

class ContractsExtractor : public llvm::InstVisitor<ContractsExtractor> {
private:
  SmackRep& rep;
  ProcDecl& proc;
  
  vector<const Expr*> slices;

public:
  ContractsExtractor(SmackRep& r, ProcDecl& d) : rep(r), proc(d) {}
  void visitCallInst(llvm::CallInst& ci);

  Expr* sliceExpr(llvm::Value* v);
  vector<const Expr*>& getSlices() { return slices; }
};

}
