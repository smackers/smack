#include "smack/Prelude.h"
#include "smack/Naming.h"
#include "smack/SmackOptions.h"
#include "smack/Regions.h"
#include "smack/BoogieAst.h"

namespace smack {

std::string getIntegerTypeName(unsigned width) {
  return "i" + std::to_string(width);
}

std::string getBvTypeName(unsigned width) {
  return "bv" + std::to_string(width);
}

std::string makeVarName(unsigned i) {
  return "i" + std::to_string(i);
}

const Expr* makeVarExpr(unsigned i) {
  return Expr::id(makeVarName(i));
}

template <class T, class U>
std::list<T> makeListOfElems(unsigned numElems, U makeElem) {
  std::list<T> elemList;
  for (unsigned i = 1; i <= numElems; ++i) {
    elemList.emplace_back(makeElem(i));
  }
  return elemList;
}

std::list<Binding> makeVars(unsigned numVars, std::string type) {
  return makeListOfElems<Binding>(numVars,
    [&](unsigned i) -> Binding { return {makeVarName(i), type}; });
}

std::list<const Expr*> makeVarExprs(unsigned numExprs) {
  return makeListOfElems<const Expr*>(numExprs, &makeVarExpr);
}

const Attr* makeBuiltinAttr(std::string arg) {
  return Attr::attr("builtin", arg);
}

const Attr* makeBvbuiltinAttr(std::string arg) {
  return Attr::attr("bvbuiltin", arg);
}

const Attr* makeInlineAttr() {
  return Attr::attr("inline");
}

//e.g.: function $not.i1(i1: i1) returns (i1);
FuncDecl* uninterpretedUnaryOp(unsigned width, std::string name) {
  std::string type = getIntegerTypeName(width);
  return Decl::function(indexedName(name, {type}), makeVars(1, type),
    type, nullptr, {});
}

//e.g.: function $shl.i1(i1: i1, i2: i1) returns (i1);
FuncDecl* uninterpretedBinaryOp(unsigned width, std::string name) {
  std::string type = getIntegerTypeName(width);
  return Decl::function(indexedName(name, {type}), makeVars(2, type),
    type, nullptr, {});
}

//e.g.: function {:inline} $add.i1(i1: i1, i2: i1) returns (i1) { (i1 + i2) }
FuncDecl* inlineBinaryOp(unsigned width, std::string name,
                         const Expr* body) {
  std::string type = getIntegerTypeName(width);
  return Decl::function(indexedName(name, {type}), makeVars(2, type),
    type, body, {makeInlineAttr()});
}

//e.g.: function {:builtin "div"} $sdiv.i1(i1: i1, i2: i1) returns (i1);
FuncDecl* builtinBinaryOp(unsigned width, std::string builtinName,
                          std::string name) {
  std::string type = getIntegerTypeName(width);
  return Decl::function(indexedName(name, {type}), makeVars(2, type),
    type, nullptr, {makeBuiltinAttr(builtinName)});
}

//e.g.: function {:bvbuiltin "bvnot"} $not.bv1(i1: bv1) returns (bv1);
FuncDecl* bvbuiltinUnaryOp(unsigned width, std::string builtinName,
                           std::string name) {
  std::string type = getBvTypeName(width);
  return Decl::function(indexedName(name, {type}), makeVars(1, type),
    type, nullptr, {makeBvbuiltinAttr(builtinName)});
}

//e.g.: function {:bvbuiltin "bvadd"} $add.bv1(i1: bv1, i2: bv1) returns (bv1);
FuncDecl* bvbuiltinBinaryOp(unsigned width, std::string builtinName,
                            std::string name) {
  std::string type = getBvTypeName(width);
  return Decl::function(indexedName(name, {type}), makeVars(2, type),
    type, nullptr, {makeBvbuiltinAttr(builtinName)});
}

//e.g.: function {:inline} $ule.i1.bool(i1: i1, i2: i1) returns (bool)
//        { (i1 <= i2) }
FuncDecl* inlineBinaryComp(unsigned width, std::string name,
                           const Expr* body) {
  std::string type = getIntegerTypeName(width);
  return Decl::function(indexedName(name, {type, Naming::BOOL_TYPE}),
    makeVars(2, type), Naming::BOOL_TYPE, body, {makeInlineAttr()});
}

//e.g.: function {:inline} $eq.bv1.bool(i1: bv1, i2: bv1) returns (bool)
//        { (i1 == i2) }
FuncDecl* inlineBinaryBvComp(unsigned width, std::string name,
                             const Expr* body) {
  std::string type = getBvTypeName(width);
  return Decl::function(indexedName(name, {type, Naming::BOOL_TYPE}),
    makeVars(2, type), Naming::BOOL_TYPE, body, {makeInlineAttr()});
}

//e.g.: function {:bvbuiltin "bvule"} $ule.bv1.bool(i1: bv1, i2: bv1)
//        returns (bool);
FuncDecl* bvbuiltinBinaryComp(unsigned width, std::string builtinName,
                              std::string name) {
  std::string type = getBvTypeName(width);
  return Decl::function(indexedName(name, {type, Naming::BOOL_TYPE}),
    makeVars(2, type), Naming::BOOL_TYPE, nullptr,
    {makeBvbuiltinAttr(builtinName)});
}

//e.g.: function {:inline} $ule.i1(i1: i1, i2: i1) returns (i1)
//        { if $ule.i1.bool(i1, i2) then 1 else 0 }
FuncDecl* inlineBinaryPred(unsigned width, std::string name) {
  std::string type = getIntegerTypeName(width);

  const Expr* body = Expr::if_then_else(
    Expr::fn(indexedName(name, {type, Naming::BOOL_TYPE}),
      makeVarExprs(2)),
    Expr::lit(1ll), Expr::lit(0ll));

  return Decl::function(indexedName(name, {type}), makeVars(2, type),
    makeVarName(1), body, {makeInlineAttr()});
}

//e.g.: function {:inline} $eq.bv1(i1: bv1, i2: bv1) returns (bv1)
//        { if $eq.bv1.bool(i1, i2) then 1bv1 else 0bv1 }
FuncDecl* inlineBinaryBvPred(unsigned width, std::string name) {
  std::string type = getBvTypeName(width);

  const Expr* body = Expr::if_then_else(
    Expr::fn(indexedName(name, {type, Naming::BOOL_TYPE}),
      makeVarExprs(2)),
    Expr::lit(1, 1), Expr::lit(0, 1));

  return Decl::function(indexedName(name, {type}), makeVars(2, type),
    "bv1", body, {makeInlineAttr()});
}

//e.g.: function {:inline} $load.i1(M: [ref] i1, p: ref) returns (i1)
//        { M[p] }
FuncDecl* safeLoadOp(unsigned width, const Expr* body) {
  std::string type = getIntegerTypeName(width);
  return Decl::function(indexedName("$load", {type}),
    {{"M", "[ref] " + type}, {"p", "ref"}}, type, body,
    {makeInlineAttr()});
}

//e.g.: function {:inline} $store.i1(M: [ref] i1, p: ref, v: i1)
//        returns ([ref] i1) { M[p := v] }
FuncDecl* safeStoreOp(unsigned width, const Expr* body) {
  std::string type = getIntegerTypeName(width);
  return Decl::function(indexedName("$store", {type}),
    {{"M", "[ref] " + type}, {"p", "ref"}, {"v", type}}, "[ref] " + type, body,
    {makeInlineAttr()});
}

//e.g.: function {:inline} $load.bv1(M: [ref] bv1, p: ref) returns (bv1)
//        { M[p] }
FuncDecl* safeLoadBvOp(unsigned width, const Expr* body) {
  std::string type = getBvTypeName(width);
  return Decl::function(indexedName("$load", {type}),
    {{"M", "[ref] " + type}, {"p", "ref"}}, type, body,
    {makeInlineAttr()});
}

//e.g.: function {:inline} $store.bv1(M: [ref] bv1, p: ref, v: bv1)
//        returns ([ref] bv1) { M[p := v] }
FuncDecl* safeStoreBvOp(unsigned width, const Expr* body) {
  std::string type = getBvTypeName(width);
  return Decl::function(indexedName("$store", {type}),
    {{"M", "[ref] " + type}, {"p", "ref"}, {"v", type}}, "[ref] " + type, body,
    {makeInlineAttr()});
}

//e.g.: function {:inline} $min.bv1(i1: bv1, i2: bv1) returns (bv1)
//        { if $slt.bv1.bool(i1, i2) then i1 else i2 }
FuncDecl* inlineBvbuiltinBinarySelect(unsigned width,
                                      std::string name,
                                      std::string name2) {
  std::string type = getBvTypeName(width);

  const Expr* body = Expr::if_then_else(
    Expr::fn(indexedName(name2, {type, Naming::BOOL_TYPE}),
      makeVarExprs(2)),
    makeVarExpr(1), makeVarExpr(2));

  return Decl::function(indexedName(name, {type}), makeVars(2, type),
    type, body, {makeInlineAttr()});
}

//e.g.: function {:inline} $ule.bv1(i1: bv1, i2: bv1) returns (bv1)
//        { if $ule.bv1.bool(i1, i2) then 1bv1 else 0bv1 }
FuncDecl* inlineBvbuiltinBinaryPred(unsigned width,
                                    std::string name) {
  std::string type = getBvTypeName(width);

  const Expr* body = Expr::if_then_else(
    Expr::fn(indexedName(name, {type, Naming::BOOL_TYPE}),
      makeVarExpr(1), makeVarExpr(2)),
    Expr::lit(1, 1), Expr::lit(0, 1));

  return Decl::function(indexedName(name, {type}), makeVars(2, type),
    "bv1", body, {makeInlineAttr()});
}

//e.g.: function {:inline} $zext.i1.i5(i1: i1) returns (i5) { i1 }
FuncDecl* inlineConversion(unsigned width, unsigned width2,
                           std::string name, const Expr* body) {
  std::string type = getIntegerTypeName(width);
  std::string type2 = getIntegerTypeName(width2);
  return Decl::function(indexedName(name, {type, type2}),
    makeVars(1, type), type2, body, {makeInlineAttr()});
}

//e.g.: function {:inline} $trunc.i5.i1(i1: i5) returns (i1) { i1 }
FuncDecl* truncOp(unsigned width, unsigned width2) {
  std::string type = getIntegerTypeName(width);
  std::string type2 = getIntegerTypeName(width2);

  const Expr* body = makeVarExpr(1);

  return Decl::function(indexedName("$trunc", {type, type2}),
    makeVars(1, type), type2, body, {makeInlineAttr()});
}

//e.g.: function {:inline} $trunc.bv5.bv1(i1: bv5) returns (bv1) { i1[1:0] }
FuncDecl* truncBvOp(unsigned width, unsigned width2) {
  std::string type = getBvTypeName(width);
  std::string type2 = getBvTypeName(width2);

  const Expr* body =
    Expr::id(makeVarName(1) + "[" + std::to_string(width2) + ":0]");

  return Decl::function(indexedName("$trunc", {type, type2}),
    makeVars(1, type), type2, body, {makeInlineAttr()});
}

std::string getBytewisePointerStorageStr() {
  std::stringstream s;
  s << "// Bytewise pointer storage" << "\n";
  s << "function {:inline} $load.bytes.ref(M: [ref] bv8, p: ref) "
    << "returns (ref) { $i2p.bv64.ref($load.bytes.bv64(M, p)) }"
    << "\n";
  s << "function {:inline} $store.bytes.ref(M: [ref] bv8, p: ref, v: ref)"
    << "returns ([ref] bv8) { $store.bytes.bv64(M,p,$p2i.ref.bv64(v)) }"
    << "\n";
  return s.str();
}

std::string Prelude::getPrelude() {
  const std::vector<unsigned> INTEGER_SIZES {
    1, 5, 6, 8, 16, 24, 32, 40, 48, 56, 64, 80, 88, 96, 128, 160, 256
  };

  const std::vector<unsigned> REF_CONSTANTS {
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 1024
  };

  const std::vector<std::string> BINARY_OPS {
    "add", "sub", "mul", "sdiv", "smod", "srem", "udiv",
    "urem", "shl", "lshr", "ashr", "and", "or", "xor", "nand"
  };

  const std::vector<std::string> COMP_OPS {
    "ule", "ult", "uge", "ugt", "sle", "slt", "sge", "sgt"
  };

  const std::vector<std::string> EQ_OPS {"eq", "ne"};

  const std::vector<BinExpr::Binary> BINARY_OPS_BODY {
    BinExpr::Plus, BinExpr::Minus, BinExpr::Times
  };

  const std::vector<BinExpr::Binary> COMP_OPS_BODY {
    BinExpr::Lte, BinExpr::Lt, BinExpr::Gte, BinExpr::Gt,
    BinExpr::Lte, BinExpr::Lt, BinExpr::Gte, BinExpr::Gt
  };

  const std::vector<BinExpr::Binary> EQ_OPS_BODY {BinExpr::Eq, BinExpr::Neq};

  std::stringstream s;

  s << "// Basic types" << "\n";
  for (unsigned size : INTEGER_SIZES)
    s << Decl::typee(getIntegerTypeName(size),"int") << "\n";
  s << Decl::typee(Naming::PTR_TYPE, rep.pointerType()) << "\n";
  if (SmackOptions::FloatEnabled) {
    s << Decl::typee(Naming::HALF_TYPE, "float11e5") << "\n";
    s << Decl::typee(Naming::FLOAT_TYPE, "float24e8") << "\n";
    s << Decl::typee(Naming::DOUBLE_TYPE, "float53e11") << "\n";
    s << Decl::typee(Naming::LONG_DOUBLE_TYPE, "float65e15") << "\n";
  } else {
    s << Decl::typee(Naming::UNINTERPRETED_FLOAT_TYPE, "") << "\n";
  }
  s << "\n";

  s << "// Basic constants" << "\n";
  s << Decl::constant("$0",rep.intType(32)) << "\n";
  s << Decl::axiom(Expr::eq(Expr::id("$0"),rep.integerLit(0ULL,32))) << "\n";
  s << Decl::constant("$1",rep.intType(32)) << "\n";
  s << Decl::axiom(Expr::eq(Expr::id("$1"),rep.integerLit(1ULL,32))) << "\n";

  for (unsigned i : REF_CONSTANTS) {
    std::stringstream t;
    s << "const $" << i << ".ref: ref;" << "\n";
    t << "$" << i << ".ref";
    s << Decl::axiom(Expr::eq(Expr::id(t.str()),
      rep.pointerLit((unsigned long long) i)))
      << "\n";
  }
  s << "\n";

  s << "// Memory maps (" << rep.regions->size() << " regions)" << "\n";
  for (auto M : rep.memoryMaps())
    s << "var " << M.first << ": " << M.second << ";" << "\n";

  s << "\n";

  s << "// Memory address bounds" << "\n";
  s << Decl::axiom(Expr::eq(Expr::id(Naming::GLOBALS_BOTTOM),
    rep.pointerLit(rep.globalsOffset)))
    << "\n";
  s << Decl::axiom(
    Expr::eq(Expr::id(Naming::EXTERNS_BOTTOM),
      Expr::fn("$add.ref", Expr::id(Naming::GLOBALS_BOTTOM),
        rep.pointerLit(rep.externsOffset))))
    << "\n";
  unsigned long long malloc_top;
  if (rep.ptrSizeInBits == 32)
    malloc_top = 2147483647UL;
  else if (rep.ptrSizeInBits == 64)
    malloc_top = 9223372036854775807UL;
  else
    llvm_unreachable("Unexpected pointer bit width.");
  s << Decl::axiom(Expr::eq(Expr::id(Naming::MALLOC_TOP),
    rep.pointerLit(malloc_top)))
    << "\n";
  s << "\n";

  if (SmackOptions::MemorySafety) {
    s << "// Global allocations" << "\n";
    std::list<const Stmt*> stmts;
    for (auto E : rep.globalAllocations)
      stmts.push_back(Stmt::call("$galloc",
        {rep.expr(E.first), rep.pointerLit(E.second)}));
    s << Decl::procedure("$global_allocations", {}, {}, {},
      {Block::block("", stmts)})
      << "\n";
    s << "\n";
  }

  s << "// Bitstd::vector-integer conversions" << "\n";
  std::string b = std::to_string(rep.ptrSizeInBits);
  std::string bt = "bv" + b;
  std::string it = "i" + b;
  s << Decl::function(indexedName("$int2bv",{rep.ptrSizeInBits}),
    {{"i",it}}, bt, nullptr, {makeBuiltinAttr("(_ int2bv " + b + ")")})
    << "\n";
  if (SmackOptions::BitPrecise) {
    s << Decl::function(indexedName("$bv2uint",{rep.ptrSizeInBits}),
      {{"i",bt}}, it, nullptr, {makeBuiltinAttr("bv2int")})
      << "\n";
    const Expr* arg = Expr::id("i");
    const Expr* uint = Expr::fn(indexedName("$bv2uint",
      {rep.ptrSizeInBits}), arg);
    std::string offset;
    if (rep.ptrSizeInBits == 32)
      offset = "4294967296";
    else if (rep.ptrSizeInBits == 64)
      offset = "18446744073709551616";
    else
      llvm_unreachable("Unexpected pointer bit width.");
    s << Decl::function(indexedName("$bv2int",{rep.ptrSizeInBits}),
      {{"i",bt}}, it, Expr::cond(
        Expr::fn(indexedName("$slt", {bt, Naming::BOOL_TYPE}),
          {arg, Expr::lit(0ULL, rep.ptrSizeInBits)}),
        Expr::fn(indexedName("$sub", {it}), {uint, Expr::lit(offset, 0U)}),
        uint),
      {makeInlineAttr()});
  } else
    s << Decl::function(indexedName("$bv2int",{rep.ptrSizeInBits}),
      {{"i",bt}}, it, nullptr, {makeBuiltinAttr("bv2int")})
      << "\n";
  s << "\n";

  if (SmackOptions::BitPrecise) {
    // XXX TODO don't assume 64-bit pointers TODO XXX
    s << getBytewisePointerStorageStr();
  }

  s << "// Pointer-number conversions" << "\n";
  for (unsigned i = 8; i <= 64; i <<= 1) {
    s << Decl::function(indexedName("$p2i", {Naming::PTR_TYPE,
        rep.intType(i)}), {{"p",Naming::PTR_TYPE}}, rep.intType(i),
      rep.pointerToInteger(Expr::id("p"),i), {makeInlineAttr()})
      << "\n";
    s << Decl::function(indexedName("$i2p", {rep.intType(i),
        Naming::PTR_TYPE}), {{"i",rep.intType(i)}}, Naming::PTR_TYPE,
      rep.integerToPointer(Expr::id("i"),i), {makeInlineAttr()})
      << "\n";
  }
  s << "\n";

  s << "// Pointer predicates" << "\n";
  const std::vector<std::string> predicates {
    "$eq", "$ne", "$ugt", "$uge", "$ult",
    "$ule", "$sgt", "$sge", "$slt","$sle"
  };
  for (auto pred : predicates) {
    s << Decl::function(indexedName(pred,{Naming::PTR_TYPE}),
      {{"p1",Naming::PTR_TYPE}, {"p2",Naming::PTR_TYPE}}, rep.intType(1),
      Expr::cond(
        Expr::fn(indexedName(pred,{rep.pointerType(),Naming::BOOL_TYPE}),
          {Expr::id("p1"),Expr::id("p2")}),
        rep.integerLit(1LL,1),
        rep.integerLit(0LL,1)),
      {makeInlineAttr()})
      << "\n";
    s << Decl::function(
      indexedName(pred,{Naming::PTR_TYPE, Naming::BOOL_TYPE}),
      {{"p1",Naming::PTR_TYPE}, {"p2", Naming::PTR_TYPE}}, Naming::BOOL_TYPE,
      Expr::fn(indexedName(pred, {rep.pointerType(),Naming::BOOL_TYPE}),
        {Expr::id("p1"), Expr::id("p2")}),
      {makeInlineAttr()})
      << "\n";
  }
  s << "\n";

  s << "// Pointer operations" << "\n";
  const std::vector<std::string> operations = {"$add", "$sub", "$mul"};
  for (auto op : operations) {
    s << Decl::function(indexedName(op,{Naming::PTR_TYPE}),
      {{"p1",Naming::PTR_TYPE},{"p2",Naming::PTR_TYPE}}, Naming::PTR_TYPE,
      Expr::fn(indexedName(op,{rep.pointerType()}),
        {Expr::id("p1"), Expr::id("p2")}),
      {makeInlineAttr()})
      << "\n";
  }
  s << "\n";

  for (size_t s1 = 0; s1 < INTEGER_SIZES.size(); ++s1) {
    const unsigned &size = INTEGER_SIZES[s1];

    for (size_t i = 0; i < BINARY_OPS.size(); ++i) {
      const std::string &op = BINARY_OPS[i];
      s << bvbuiltinBinaryOp(size, "bv" + op, "$" + op) << "\n";
      if (i <= 2) {
        s << inlineBinaryOp(size, "$" + op,
          new BinExpr(BINARY_OPS_BODY[i], makeVarExpr(1), makeVarExpr(2)))
          << "\n";
      } else if (i <= 7) {
        s << builtinBinaryOp(size, op.substr(1), "$" + op) << "\n";
      } else {
        s << uninterpretedBinaryOp(size, "$" + op) << "\n";
      }
    }

    for (size_t i = 0; i < COMP_OPS.size(); ++i) {
      const std::string &op = COMP_OPS[i];
      s << bvbuiltinBinaryComp(size, "bv" + op, "$" + op) << "\n";
      s << inlineBvbuiltinBinaryPred(size, "$" + op) << "\n";
      s << inlineBinaryComp(size, "$" + op,
        new BinExpr(COMP_OPS_BODY[i], makeVarExpr(1), makeVarExpr(2))) << "\n";
      s << inlineBinaryPred(size, "$" + op) << "\n";
    }

    for (size_t i = 0; i < EQ_OPS.size(); ++i) {
      const std::string &op = EQ_OPS[i];
      s << inlineBinaryBvComp(size, "$" + op,
        new BinExpr(EQ_OPS_BODY[i], makeVarExpr(1), makeVarExpr(2))) << "\n";
      s << inlineBinaryBvPred(size, "$" + op) << "\n";
      s << inlineBinaryComp(size, "$" + op,
        new BinExpr(EQ_OPS_BODY[i], makeVarExpr(1), makeVarExpr(2))) << "\n";
      s << inlineBinaryPred(size, "$" + op) << "\n";
    }

    s << inlineBvbuiltinBinarySelect(size, "$min", "$slt") << "\n";
    s << inlineBvbuiltinBinarySelect(size, "$max", "$sgt") << "\n";
    s << inlineBvbuiltinBinarySelect(size, "$umin", "$ult") << "\n";
    s << inlineBvbuiltinBinarySelect(size, "$umax", "$ugt") << "\n";

    s << inlineBinaryOp(size, "$smin", Expr::fn("$min", makeVarExprs(2)))
      << "\n";
    s << inlineBinaryOp(size, "$smax", Expr::fn("$max", makeVarExprs(2)))
      << "\n";
    s << inlineBinaryOp(size, "$umin", Expr::fn("$min", makeVarExprs(2)))
      << "\n";
    s << inlineBinaryOp(size, "$umax", Expr::fn("$max", makeVarExprs(2)))
      << "\n";

    s << bvbuiltinUnaryOp(size, "bvnot", "$not") << "\n";
    s << uninterpretedUnaryOp(size, "$not") << "\n";

    s << safeLoadOp(size, Expr::id("M[p]")) << "\n";
    s << safeLoadBvOp(size, Expr::id("M[p]")) << "\n";
    s << safeStoreOp(size, Expr::id("M[p := v]")) << "\n";
    s << safeStoreBvOp(size, Expr::id("M[p := v]")) << "\n";
  }

  for (size_t s1 = 0; s1 < INTEGER_SIZES.size(); ++s1) {
    const unsigned &size = INTEGER_SIZES[s1];
    for (size_t s2 = s1 + 1; s2 < INTEGER_SIZES.size(); ++s2) {
      const unsigned &size2 = INTEGER_SIZES[s2];
      s << truncBvOp(size2, size) << "\n";
      s << truncOp(size2, size) << "\n";

      s << inlineConversion(size, size2, "$zext", makeVarExpr(1)) << "\n";
      s << inlineConversion(size, size2, "$sext", makeVarExpr(1)) << "\n";
    }
  }

  return s.str();
}

} //namespace smack
