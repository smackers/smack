//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef SLICING_H
#define SLICING_H

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/InstVisitor.h"
#include <unordered_set>

using namespace llvm;

namespace smack {

class Naming;
class SmackRep;

class Slice;
typedef vector<Slice *> Slices;

class Slice {
  Value &value;
  BasicBlock &block;
  Function &function;
  LLVMContext &context;
  Slices &slices;
  string name;

  unordered_set<Value *> inputs;
  unordered_set<Value *> values;

public:
  Slice(Instruction &I, Slices &S, string name = "");

  void remove();

  string getName();
  const Expr *getCode(Naming *naming, SmackRep *rep);
  const Decl *getBoogieDecl(Naming *naming, SmackRep *rep);
  const Expr *getBoogieExpression(Naming *naming, SmackRep *rep);
};
} // namespace smack

#endif
