//
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/CFG.h"
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
  Slices& slices;
  static unsigned uniqueSliceId;

public:
  ContractsExtractor(SmackRep& R, ProcDecl& P, Naming& N, Slices& S)
    : rep(R), proc(P), naming(N), slices(S) {}

  void visitCallInst(CallInst& ci);

private:
  Slice* extractSlice(Value* v);

  Value* sliceIdx(LLVMContext& ctx) {
    return ConstantInt::get(Type::getInt32Ty(ctx),slices.size());
  }
};

}
