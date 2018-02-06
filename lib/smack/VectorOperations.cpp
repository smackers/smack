//
// This file is distributed under the MIT License. See LICENSE for details.
//
#define DEBUG_TYPE "vector-ops"
#include "llvm/IR/Instruction.h"
#include "smack/BoogieAst.h"
#include "smack/SmackRep.h"
#include "smack/Regions.h"
#include "smack/VectorOperations.h"
#include "smack/Naming.h"
#include "smack/Debug.h"
#include <sstream>
#include <list>

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

  std::list<Decl*> VectorOperations::type(Type *T) {
    auto VT = dyn_cast<VectorType>(T);
    assert(VT && "expected vector type");
    std::list<Decl*> decls;

    std::list< std::pair< std::string, std::string > > args;
    for (unsigned i=0; i<VT->getNumElements(); i++)
      args.push_back({field(T, i), rep->type(VT->getElementType())});

    decls.push_back(Decl::typee(rep->type(T), "", {Attr::attr("datatype")}));
    decls.push_back(Decl::function(constructor(T), args, rep->type(T), NULL, {Attr::attr("constructor")}));

    for (auto D : decls)
      rep->addAuxiliaryDeclaration(D);
    return decls;
  }

  const Expr *VectorOperations::constant(const ConstantDataVector *C) {
    auto T = C->getType();
    std::list<const Expr*> args;
    for (unsigned i = 0; i < C->getNumElements(); i++)
      args.push_back(rep->expr(C->getElementAsConstant(i)));
    return Expr::fn(constructor(T), args);
  }

  Decl *VectorOperations::inverseCastAxiom(CastInst *CI) {
    auto N = Naming::INSTRUCTION_TABLE.at(CI->getOpcode());
    auto SrcTy = CI->getOperand(0)->getType();
    auto DstTy = CI->getType();
    auto Fn = rep->opName(N, {SrcTy, DstTy});
    auto Inv = rep->opName(N, {DstTy, SrcTy});

    return Decl::axiom(Expr::forall({{"v", rep->type(SrcTy)}},
      Expr::eq(
        Expr::fn(Inv, Expr::fn(Fn, Expr::id("v"))),
        Expr::id("v"))));
  }

  FuncDecl *VectorOperations::simd(Instruction *I) {
    auto T = dyn_cast<VectorType>(I->getType());
    assert(T && "expected vector type");
    type(T);

    auto U = dyn_cast<VectorType>(I->getOperand(0)->getType());
    assert(U && "expected vector type");
    type(U);

    std::string N;
    unsigned arity;
    std::list<const Type*> Ts;
    std::list<const Type*> ETs;

    if (auto BI = dyn_cast<BinaryOperator>(I)) {
      arity = 2;
      Ts = {T};
      ETs = {T->getElementType()};
      N = Naming::INSTRUCTION_TABLE.at(I->getOpcode());

    } else if (auto UI = dyn_cast<UnaryInstruction>(I)) {
      arity = 1;
      Ts = {U, T};
      ETs = {U->getElementType(), T->getElementType()};
      N = Naming::INSTRUCTION_TABLE.at(I->getOpcode());

    } else if (auto CI = dyn_cast<CmpInst>(I)) {
      arity = 2;
      Ts = {U};
      ETs = {U->getElementType()};
      N = Naming::CMPINST_TABLE.at(CI->getPredicate());

    } else {
      llvm_unreachable("unexpected instruction");
    }

    auto FN = rep->opName(N, Ts);
    auto baseFN = rep->opName(N, ETs);

    std::list<std::pair<std::string,std::string>> params;
    for (unsigned j=1; j<=arity; j++)
      params.push_back({"v" + std::to_string(j), rep->type(U)});

    std::list<const Expr*> args;
    for (unsigned i=0; i<T->getNumElements(); i++) {
      std::list<const Expr*> operands;
      for (unsigned j=1; j<=arity; j++)
        operands.push_back(Expr::fn(selector(U,i), Expr::id("v" + std::to_string(j))));
      args.push_back(Expr::fn(baseFN, operands));
    }

    auto F = T->getNumElements() == U->getNumElements()
      ? Decl::function(FN, params, rep->type(T), Expr::fn(constructor(T), args))
      : Decl::function(FN, params, rep->type(T));

    rep->addAuxiliaryDeclaration(F);

    if (auto CI = dyn_cast<CastInst>(I))
      rep->addAuxiliaryDeclaration(inverseCastAxiom(CI));

    return F;
  }

  FuncDecl *VectorOperations::shuffle(Type *T, Type *U, std::vector<int> mask) {
    auto VT = dyn_cast<VectorType>(T);
    assert(VT && "expected vector type");
    assert(isa<VectorType>(U) && "expected vector type");
    type(T);
    type(U);

    std::stringstream FN;
    FN << rep->opName(Naming::INSTRUCTION_TABLE.at(Instruction::ShuffleVector), {T});
    for (auto m : mask)
      FN << "." << m;

    auto N = VT->getNumElements();
    std::list<const Expr*> args;
    for (int m : mask) {
      if (m < 0)
        llvm_unreachable("TODO: handle undefined mask values");

      auto idx = (unsigned) m;
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
    auto VT = dyn_cast<VectorType>(T);
    assert(VT && "expected vector type");
    type(T);

    auto FN = rep->opName(Naming::INSTRUCTION_TABLE.at(Instruction::InsertElement), {T, IT});

    auto V = rep->type(T);
    auto E = rep->type(VT->getElementType());
    auto I = rep->type(IT);
    auto F = Decl::function(FN, {{"v", V}, {"x", E}, {"i", I}}, V);
    rep->addAuxiliaryDeclaration(F);

    // A per-index axiomatization
    for (unsigned i=0; i < VT->getNumElements(); i++) {
      std::stringstream ss;
      ss << FN << "(" << i << ")";

      std::list<const Expr*> args;
      for (unsigned j=0; j < VT->getNumElements(); j++) {
        args.push_back(i == j ? Expr::id("x") : Expr::fn(selector(T,j), Expr::id("v")));
      }

      rep->addAuxiliaryDeclaration(Decl::axiom(
        Expr::forall({{"v", V}, {"x", E}}, Expr::eq(
          Expr::fn(FN, Expr::id("v"), Expr::id("x"), Expr::lit(i)),
          Expr::fn(constructor(T), args)
        )),
        ss.str()
      ));
    }

    return F;

    std::stringstream procName;
    procName << Naming::INSTRUCTION_TABLE.at(Instruction::InsertElement);
    procName << "." << rep->type(T);
    return nullptr;
  }

  FuncDecl *VectorOperations::extract(Type *T, Type *IT) {
    auto VT = dyn_cast<VectorType>(T);
    assert(VT && "expected vector type");
    type(T);

    auto FN = rep->opName(Naming::INSTRUCTION_TABLE.at(Instruction::ExtractElement), {T, IT});

    auto V = rep->type(T);
    auto I = rep->type(IT);
    auto E = rep->type(VT->getElementType());
    auto F = Decl::function(FN, {{"v", V}, {"i", I}}, E);
    rep->addAuxiliaryDeclaration(F);

    // A per-index axiomatization
    for (unsigned i=0; i < VT->getNumElements(); i++) {
      std::stringstream ss;
      ss << FN << "(" << i << ")";
      rep->addAuxiliaryDeclaration(Decl::axiom(
        Expr::forall({{"v", V}}, Expr::eq(
          Expr::fn(FN, Expr::id("v"), Expr::lit(i)),
          Expr::fn(selector(T, i), Expr::id("v"))
        )),
        ss.str()
      ));
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
    auto F = (MT == ET)
      ? Decl::function(FN, {{"M", M}, {"p", P}}, E,  Expr::sel(Expr::id("M"), Expr::id("p")))
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
    auto F = (MT == ET)
      ? Decl::function(FN, {{"M", M}, {"p", P}, {"v", E}}, M, Expr::upd(Expr::id("M"), Expr::id("p"), Expr::id("v")))
      : Decl::function(FN, {{"M", M}, {"p", P}, {"v", E}}, M);
    rep->addAuxiliaryDeclaration(F);
    return F;
  }
}
