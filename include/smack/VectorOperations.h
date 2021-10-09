//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef VECTOROPERATIONS_H
#define VECTOROPERATIONS_H

#include "smack/BoogieAst.h"
#include "smack/SmackRep.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Type.h"
#include <list>

using namespace llvm;

namespace smack {
class VectorOperations {
  SmackRep *rep;
  std::string constructor(Type *T);
  std::string field(Type *T, unsigned idx);
  std::string selector(Type *T, unsigned idx);

  FuncDecl *cast(unsigned OpCode, Type *SrcTy, Type *DstTy);
  Decl *inverseAxiom(unsigned OpCode, Type *SrcTy, Type *DstTy);
  FuncDecl *binary(unsigned OpCode, FixedVectorType *T);
  FuncDecl *cmp(CmpInst::Predicate P, FixedVectorType *T);

public:
  VectorOperations(SmackRep *rep) : rep(rep) {}
  std::list<Decl *> type(Type *T);
  const Expr *constant(const ConstantDataVector *C);
  const Expr *constant(const ConstantAggregateZero *C);

  FuncDecl *cast(CastInst *I);
  FuncDecl *binary(BinaryOperator *I);
  FuncDecl *cmp(CmpInst *I);
  FuncDecl *shuffle(Type *T, Type *U, std::vector<int> mask);
  FuncDecl *insert(Type *T, Type *IT);
  FuncDecl *extract(Type *T, Type *IT);
  FuncDecl *load(const Value *V);
  FuncDecl *store(const Value *V);
};
} // namespace smack

#endif // VECTOROPERATIONS_H
