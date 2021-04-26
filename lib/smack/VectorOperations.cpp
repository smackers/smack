//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "vector-ops"
#include "smack/VectorOperations.h"
#include "smack/Debug.h"
#include "smack/Naming.h"
#include "smack/Regions.h"
#include "llvm/IR/Instruction.h"
#include <sstream>

using namespace llvm;

namespace smack {
std::string VectorOperations::constructor(Type *T) {
  return "mk." + rep->type(T);
}

std::string VectorOperations::field(Type *T, unsigned idx) {
  std::stringstream ss;
  ss << "i" << idx;
  return ss.str();
}

std::string VectorOperations::selector(Type *T, unsigned idx) {
  return field(T, idx) + "#" + constructor(T);
}

std::list<Decl *> VectorOperations::type(Type *T) {
  auto VT = dyn_cast<FixedVectorType>(T);
  assert(VT && "expected vector type");
  std::list<Decl *> decls;

  std::list<std::pair<std::string, std::string>> args;
  for (unsigned i = 0; i < VT->getNumElements(); i++)
    args.push_back({field(T, i), rep->type(VT->getElementType())});

  decls.push_back(Decl::typee(rep->type(T), "", {Attr::attr("datatype")}));
  decls.push_back(Decl::function(constructor(T), args, rep->type(T), NULL,
                                 {Attr::attr("constructor")}));

  for (auto D : decls)
    rep->addAuxiliaryDeclaration(D);
  return decls;
}

const Expr *VectorOperations::constant(const ConstantDataVector *C) {
  auto T = C->getType();
  std::list<const Expr *> args;
  for (unsigned i = 0; i < C->getNumElements(); i++)
    args.push_back(rep->expr(C->getElementAsConstant(i)));
  return Expr::fn(constructor(T), args);
}

const Expr *VectorOperations::constant(const ConstantAggregateZero *C) {
  auto T = C->getType();
  std::list<const Expr *> args;
  for (unsigned i = 0; i < C->getNumElements(); i++)
    args.push_back(rep->expr(C->getElementValue(i)));
  return Expr::fn(constructor(T), args);
}

FuncDecl *VectorOperations::cast(unsigned OpCode, Type *SrcTy, Type *DstTy) {
  auto SrcVecTy = dyn_cast<FixedVectorType>(SrcTy);
  auto DstVecTy = dyn_cast<FixedVectorType>(DstTy);
  assert((SrcVecTy || DstVecTy) && "Expected a vector type");

  auto FnName =
      rep->opName(Naming::INSTRUCTION_TABLE.at(OpCode), {SrcTy, DstTy});
  const Expr *Body;

  if (!SrcVecTy && DstVecTy && DstVecTy->getNumElements() == 1)
    Body = Expr::fn(constructor(DstVecTy), Expr::id("v"));
  else if (SrcVecTy && SrcVecTy->getNumElements() == 1 && !DstVecTy)
    Body = Expr::fn(selector(SrcVecTy, 0), Expr::id("v"));
  else
    Body = nullptr;

  return Decl::function(FnName, {{"v", rep->type(SrcTy)}}, rep->type(DstTy),
                        Body);
}

Decl *VectorOperations::inverseAxiom(unsigned OpCode, Type *SrcTy,
                                     Type *DstTy) {
  auto Fn = rep->opName(Naming::INSTRUCTION_TABLE.at(OpCode), {SrcTy, DstTy});
  auto Inv = rep->opName(Naming::INSTRUCTION_TABLE.at(OpCode), {DstTy, SrcTy});
  return Decl::axiom(
      Expr::forall(
          {{"v", rep->type(SrcTy)}},
          Expr::eq(Expr::fn(Inv, Expr::fn(Fn, Expr::id("v"))), Expr::id("v"))),
      Fn + "inverse");
}

FuncDecl *VectorOperations::binary(unsigned OpCode, FixedVectorType *T) {
  auto FnName = rep->opName(Naming::INSTRUCTION_TABLE.at(OpCode), {T});
  auto FnBase =
      rep->opName(Naming::INSTRUCTION_TABLE.at(OpCode), {T->getElementType()});
  std::list<const Expr *> Args;
  for (unsigned i = 0; i < T->getNumElements(); i++) {
    Args.push_back(
        Expr::fn(FnBase, {Expr::fn(selector(T, i), Expr::id("v1")),
                          Expr::fn(selector(T, i), Expr::id("v2"))}));
  }
  return Decl::function(FnName, {{"v1", rep->type(T)}, {"v2", rep->type(T)}},
                        rep->type(T), Expr::fn(constructor(T), Args));
}

FuncDecl *VectorOperations::cmp(CmpInst::Predicate P, FixedVectorType *T) {
  auto FnName = rep->opName(Naming::CMPINST_TABLE.at(P), {T});
  auto FnBase = rep->opName(Naming::CMPINST_TABLE.at(P), {T->getElementType()});
  std::list<const Expr *> Args;
  for (unsigned i = 0; i < T->getNumElements(); i++) {
    Args.push_back(
        Expr::fn(FnBase, {Expr::fn(selector(T, i), Expr::id("v1")),
                          Expr::fn(selector(T, i), Expr::id("v2"))}));
  }
  return Decl::function(
      FnName, {{"v1", rep->type(T)}, {"v2", rep->type(T)}},
      rep->type(FixedVectorType::get(IntegerType::get(T->getContext(), 1),
                                     T->getNumElements())),
      Expr::fn(constructor(T), Args));
}

FuncDecl *VectorOperations::cast(CastInst *I) {
  SDEBUG(errs() << "simd-cast: " << *I << "\n");
  auto F = cast(I->getOpcode(), I->getSrcTy(), I->getDestTy());
  auto G = cast(I->getOpcode(), I->getDestTy(), I->getSrcTy());
  auto A = inverseAxiom(I->getOpcode(), I->getSrcTy(), I->getDestTy());
  auto B = inverseAxiom(I->getOpcode(), I->getDestTy(), I->getSrcTy());
  if (isa<FixedVectorType>(I->getSrcTy()))
    type(I->getSrcTy());
  if (isa<FixedVectorType>(I->getDestTy()))
    type(I->getDestTy());
  rep->addAuxiliaryDeclaration(F);
  rep->addAuxiliaryDeclaration(G);
  rep->addAuxiliaryDeclaration(A);
  rep->addAuxiliaryDeclaration(B);
  return F;
}

FuncDecl *VectorOperations::binary(BinaryOperator *I) {
  SDEBUG(errs() << "simd-binary: " << *I << "\n");
  auto T = dyn_cast<FixedVectorType>(I->getType());
  assert(T && T == I->getOperand(0)->getType() &&
         "expected equal vector types");
  auto F = binary(I->getOpcode(), T);
  type(T);
  rep->addAuxiliaryDeclaration(F);
  return F;
}

FuncDecl *VectorOperations::cmp(CmpInst *I) {
  SDEBUG(errs() << "simd-binary: " << *I << "\n");
  auto T = dyn_cast<FixedVectorType>(I->getOperand(0)->getType());
  assert(T && "expected vector type");
  auto F = cmp(I->getPredicate(), T);
  type(T);
  type(FixedVectorType::get(IntegerType::get(T->getContext(), 1),
                            T->getNumElements()));
  rep->addAuxiliaryDeclaration(F);
  return F;
}

FuncDecl *VectorOperations::shuffle(Type *T, Type *U, std::vector<int> mask) {
  auto VT = dyn_cast<FixedVectorType>(T);
  assert(VT && "expected vector type");
  assert(isa<FixedVectorType>(U) && "expected vector type");
  type(T);
  type(U);

  std::stringstream FN;
  FN << rep->opName(Naming::INSTRUCTION_TABLE.at(Instruction::ShuffleVector),
                    {T});
  for (auto m : mask)
    FN << "." << m;

  auto N = VT->getNumElements();
  std::list<const Expr *> args;
  for (int m : mask) {
    if (m < 0)
      llvm_unreachable("TODO: handle undefined mask values");

    auto idx = (unsigned)m;
    if (idx < N)
      args.push_back(Expr::fn(selector(T, idx), Expr::id("v1")));
    else
      args.push_back(Expr::fn(selector(T, idx - N), Expr::id("v2")));
  }

  auto V = rep->type(T);
  auto F = Decl::function(FN.str(), {{"v1", V}, {"v2", V}}, rep->type(U),
                          Expr::fn(constructor(U), args));
  rep->addAuxiliaryDeclaration(F);
  return F;
}

FuncDecl *VectorOperations::insert(Type *T, Type *IT) {
  auto VT = dyn_cast<FixedVectorType>(T);
  assert(VT && "expected vector type");
  type(T);

  auto FN = rep->opName(
      Naming::INSTRUCTION_TABLE.at(Instruction::InsertElement), {T, IT});

  auto V = rep->type(T);
  auto E = rep->type(VT->getElementType());
  auto I = rep->type(IT);
  auto F = Decl::function(FN, {{"v", V}, {"x", E}, {"i", I}}, V);
  rep->addAuxiliaryDeclaration(F);

  // A per-index axiomatization
  for (unsigned i = 0; i < VT->getNumElements(); i++) {
    std::stringstream ss;
    ss << FN << "(" << i << ")";

    std::list<const Expr *> args;
    for (unsigned j = 0; j < VT->getNumElements(); j++) {
      args.push_back(i == j ? Expr::id("x")
                            : Expr::fn(selector(T, j), Expr::id("v")));
    }

    rep->addAuxiliaryDeclaration(Decl::axiom(
        Expr::forall(
            {{"v", V}, {"x", E}},
            Expr::eq(Expr::fn(FN, Expr::id("v"), Expr::id("x"), Expr::lit(i)),
                     Expr::fn(constructor(T), args))),
        ss.str()));
  }

  return F;

  std::stringstream procName;
  procName << Naming::INSTRUCTION_TABLE.at(Instruction::InsertElement);
  procName << "." << rep->type(T);
  return nullptr;
}

FuncDecl *VectorOperations::extract(Type *T, Type *IT) {
  auto VT = dyn_cast<FixedVectorType>(T);
  assert(VT && "expected vector type");
  type(T);

  auto FN = rep->opName(
      Naming::INSTRUCTION_TABLE.at(Instruction::ExtractElement), {T, IT});

  auto V = rep->type(T);
  auto I = rep->type(IT);
  auto E = rep->type(VT->getElementType());
  auto F = Decl::function(FN, {{"v", V}, {"i", I}}, E);
  rep->addAuxiliaryDeclaration(F);

  // A per-index axiomatization
  for (unsigned i = 0; i < VT->getNumElements(); i++) {
    std::stringstream ss;
    ss << FN << "(" << i << ")";
    rep->addAuxiliaryDeclaration(Decl::axiom(
        Expr::forall({{"v", V}},
                     Expr::eq(Expr::fn(FN, Expr::id("v"), Expr::lit(i)),
                              Expr::fn(selector(T, i), Expr::id("v")))),
        ss.str()));
  }

  return F;
}

FuncDecl *VectorOperations::load(const Value *V) {
  auto PT = dyn_cast<PointerType>(V->getType());
  assert(PT && "expected pointer type");
  auto ET = PT->getElementType();
  type(ET);

  auto R = rep->regions->idx(V);
  auto MT = rep->regions->get(R).getType();
  MT || (MT = IntegerType::get(V->getContext(), 8));
  auto FN = rep->opName(Naming::LOAD, {ET, MT});
  auto M = rep->memType(R);
  auto P = rep->type(PT);
  auto E = rep->type(ET);
  auto F = (MT == ET) ? Decl::function(FN, {{"M", M}, {"p", P}}, E,
                                       Expr::sel(Expr::id("M"), Expr::id("p")))
                      : Decl::function(FN, {{"M", M}, {"p", P}}, E);
  rep->addAuxiliaryDeclaration(F);
  return F;
}

FuncDecl *VectorOperations::store(const Value *V) {
  auto PT = dyn_cast<PointerType>(V->getType());
  assert(PT && "expected pointer type");
  auto ET = PT->getElementType();
  type(ET);

  auto R = rep->regions->idx(V);
  auto MT = rep->regions->get(R).getType();
  MT || (MT = IntegerType::get(V->getContext(), 8));
  auto FN = rep->opName(Naming::STORE, {ET, MT});
  auto M = rep->memType(R);
  auto P = rep->type(PT);
  auto E = rep->type(ET);
  auto F = (MT == ET) ? Decl::function(FN, {{"M", M}, {"p", P}, {"v", E}}, M,
                                       Expr::upd(Expr::id("M"), Expr::id("p"),
                                                 Expr::id("v")))
                      : Decl::function(FN, {{"M", M}, {"p", P}, {"v", E}}, M);
  rep->addAuxiliaryDeclaration(F);
  return F;
}
} // namespace smack
