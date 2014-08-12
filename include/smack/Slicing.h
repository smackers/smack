//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef SLICING_H
#define SLICING_H

#include "llvm/InstVisitor.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "smack/BoogieAst.h"
#include "smack/Naming.h"
#include "smack/SmackRep.h"
#include <unordered_set>

using namespace std;
using namespace llvm;

namespace smack {

typedef vector<const Expr*> ExpressionList;

class Slice {
  string name;
  Value& value;
  BasicBlock& block;
  Function& function;
  LLVMContext& context;

  unordered_set<Value*> inputs;
  unordered_set<Value*> values;

public:
  Slice(string name, Instruction& I);

  void remove();

  string getName();
  const Decl* getBoogieDecl(Naming& naming, SmackRep& rep, ExpressionList& exprs);
  const Expr* getBoogieExpression(Naming& naming);
};

}

#endif
