#include "smack/Prelude.h"
#include "smack/Naming.h"
#include "smack/Regions.h"
#include "smack/SmackOptions.h"
#include "llvm/ADT/APInt.h"
#include "llvm/Support/Casting.h"

#include <functional>
#include <map>
#include <tuple>

namespace smack {

// make type names such as i32
std::string getIntTypeName(unsigned width) {
  return "i" + std::to_string(width);
}

// make type names such as bv32
std::string getBvTypeName(unsigned width) {
  return "bv" + std::to_string(width);
}

// make type name rmode
std::string getRMODETypeName() { return "rmode"; }

// make floating-point type names by bit width
// when bitWidth is 0, the uninterpreted type is returned
std::string getFpTypeName(unsigned bitWidth) {
  static const std::map<unsigned, std::string> floatNameTable{
      {0, Naming::UNINTERPRETED_FLOAT_TYPE},
      {16, Naming::HALF_TYPE},
      {32, Naming::FLOAT_TYPE},
      {64, Naming::DOUBLE_TYPE},
      {80, Naming::LONG_DOUBLE_TYPE}};
  auto it = floatNameTable.find(bitWidth);
  if (it != floatNameTable.end())
    return it->second;
  else
    llvm_unreachable("invalid floating-point bit width");
}

// make type names such as [ref] i32
std::string getMapTypeName(std::string elemType) { return "[ref] " + elemType; }

// make generic type names
// when the `i` is 0, it returns the prefix
// otherwise it returns `prefix+i`
std::string makeVarName(unsigned i, std::string prefix) {
  return i ? prefix + std::to_string(i) : prefix;
}

// make var names such as i, i1
std::string makeIntVarName(unsigned i) { return makeVarName(i, "i"); }

// make var names such as p, p1
std::string makePtrVarName(unsigned i) { return makeVarName(i, "p"); }

// make var names such as f, f1
std::string makeFpVarName(unsigned i) { return makeVarName(i, "f"); }

// make var names such as M, M1
std::string makeMapVarName(unsigned i) { return makeVarName(i, "M"); }

std::string makeRMODEVarName() { return makeVarName(0, "rm"); }

// make id expr
const Expr *makeIntVarExpr(unsigned i) { return Expr::id(makeIntVarName(i)); }

const Expr *makePtrVarExpr(unsigned i) { return Expr::id(makePtrVarName(i)); }

const Expr *makeFpVarExpr(unsigned i) { return Expr::id(makeFpVarName(i)); }

const Expr *makeMapVarExpr(unsigned i) { return Expr::id(makeMapVarName(i)); }

template <class T, class U>
std::list<T> makeListOfElems(unsigned numElems, U makeElem) {
  std::list<T> elemList;
  if (numElems == 1)
    elemList.emplace_back(makeElem(0));
  else
    for (unsigned i = 1; i <= numElems; ++i) {
      elemList.emplace_back(makeElem(i));
    }
  return elemList;
}

// make bindings such as [(i,i32)], [(i1,i32),(i2,i32)]
std::list<Binding> makeIntVars(unsigned numVars, std::string type) {
  return makeListOfElems<Binding>(numVars, [&](unsigned i) -> Binding {
    return {makeIntVarName(i), type};
  });
}

// make bindings such as [(p,ref)], [(p1,ref),(p2,ref)]
std::list<Binding> makePtrVars(unsigned numVars) {
  return makeListOfElems<Binding>(numVars, [&](unsigned i) -> Binding {
    return {makePtrVarName(i), Naming::PTR_TYPE};
  });
}

// make bindings such as [(f,float)], [(f1,float),(f2,float)]
std::list<Binding> makeFpVars(unsigned numVars, unsigned bitWidth) {
  return makeListOfElems<Binding>(numVars, [&](unsigned i) -> Binding {
    return {makeFpVarName(i), getFpTypeName(bitWidth)};
  });
}

// make bindings such as [(M,[ref]T)], [(p1,[ref]T),(p2,[ref]T)]
std::list<Binding> makeMapVars(unsigned numVars, std::string elemType) {
  return makeListOfElems<Binding>(numVars, [&](unsigned i) -> Binding {
    return {makeMapVarName(i), getMapTypeName(elemType)};
  });
}

// make id exprs
std::list<const Expr *> makeIntVarExprs(unsigned numExprs) {
  return makeListOfElems<const Expr *>(numExprs, &makeIntVarExpr);
}

std::list<const Expr *> makePtrVarExprs(unsigned numExprs) {
  return makeListOfElems<const Expr *>(numExprs, &makePtrVarExpr);
}

std::list<const Expr *> makeFpVarExprs(unsigned numExprs) {
  return makeListOfElems<const Expr *>(numExprs, &makeFpVarExpr);
}

std::list<const Expr *> makeMapVarExprs(unsigned numExprs) {
  return makeListOfElems<const Expr *>(numExprs, &makeMapVarExpr);
}

// make attributes
const Attr *makeBuiltinAttr(std::string arg) {
  return Attr::attr("builtin", arg);
}

const Attr *makeBvbuiltinAttr(std::string arg) {
  return Attr::attr("bvbuiltin", arg);
}

const Attr *makeInlineAttr() { return Attr::attr("inline"); }

// declare an uninterpreted function
FuncDecl *uninterpretedOp(std::string baseName,
                          std::initializer_list<std::string> nameArgs,
                          std::list<Binding> args, std::string retType) {
  return Decl::function(indexedName(baseName, nameArgs), args, retType, nullptr,
                        {});
}

// declare a function with `:inline` attribute
FuncDecl *inlinedOp(std::string baseName,
                    std::initializer_list<std::string> nameArgs,
                    std::list<Binding> args, std::string retType,
                    const Expr *body) {
  return Decl::function(indexedName(baseName, nameArgs), args, retType, body,
                        {makeInlineAttr()});
}

// declare a function with an attribute indicating it's a built-in function
FuncDecl *builtinOp(std::string baseName, const Attr *attr,
                    std::initializer_list<std::string> nameArgs,
                    std::list<Binding> args, std::string retType) {
  return Decl::function(indexedName(baseName, nameArgs), args, retType, nullptr,
                        {attr});
}

std::string getIntLimit(unsigned size) {
  auto n = APInt(size + 1, 0);
  n.setBit(size);
  return n.toString(10, false);
}

const std::vector<unsigned> IntOpGen::INTEGER_SIZES{
    1, 5, 6, 8, 16, 24, 32, 33, 40, 48, 56, 64, 80, 88, 96, 128, 160, 256};

// floating-point layout map: bit-width -> (exponent bit-width, significand
// bit-width)
const std::map<unsigned, std::pair<unsigned, unsigned>> FpOpGen::FP_LAYOUT{
    {16, {5, 11}}, {32, {8, 24}}, {64, {11, 53}}, {80, {15, 65}}};

const std::vector<unsigned> FpOpGen::FP_BIT_WIDTHS{16, 32, 64, 80};

// make Boogie map selection expression such as
// M[p], M[$add.ref(p, 1)]
const Expr *Prelude::mapSelExpr(unsigned idx) {
  auto ptrVar = makePtrVarExpr(0);
  auto idxExpr = idx ? Expr::fn(indexedName("$add", {Naming::PTR_TYPE}), ptrVar,
                                rep.pointerLit((unsigned long long)idx))
                     : ptrVar;
  return Expr::sel(makeMapVarExpr(0), idxExpr);
}

// make Boogie map update expression such as
// M[p:=v], M[$add.ref(p,1):=v]
const Expr *Prelude::mapUpdExpr(unsigned idx, const Expr *val,
                                const Expr *map) {
  auto ptrVar = makePtrVarExpr(0);
  auto mapExpr = map ? map : makeMapVarExpr(0);
  auto idxExpr = idx ? Expr::fn(indexedName("$add", {Naming::PTR_TYPE}), ptrVar,
                                rep.pointerLit((unsigned long long)idx))
                     : ptrVar;
  return Expr::upd(mapExpr, idxExpr, val);
}

// make type-safe load functions
FuncDecl *Prelude::safeLoad(std::string elemType) {
  return inlinedOp("$load", {elemType},
                   {makeMapVars(1, elemType).front(), makePtrVars(1).front()},
                   elemType, mapSelExpr(0));
}

// make type-unsafe load functions
// argument `bytes` indicate whether the map element type is bv or int given
// the `--float` flag is enabled
FuncDecl *Prelude::unsafeLoad(std::string elemType, const Expr *body,
                              bool bytes) {
  return inlinedOp(
      "$load", {bytes ? "bytes" : "unsafe", elemType},
      {makeMapVars(1, bytes ? getBvTypeName(8) : getIntTypeName(8)).front(),
       makePtrVars(1).front()},
      elemType, body);
}

// make type-safe store functions
FuncDecl *Prelude::safeStore(Binding elemBinding) {
  auto elemType = elemBinding.second;
  auto elemExpr = Expr::id(elemBinding.first);
  return inlinedOp(
      "$store", {elemType},
      {makeMapVars(1, elemType).front(), makePtrVars(1).front(), elemBinding},
      getMapTypeName(elemType), mapUpdExpr(0, elemExpr));
}

// make type-unsafe store functions
// argument `bytes` indicate whether the map element type is bv or int given
// the `--float` flag is enabled
FuncDecl *Prelude::unsafeStore(Binding elemBinding, const Expr *body,
                               bool bytes) {
  auto elemType = elemBinding.second;
  return inlinedOp(
      "$store", {bytes ? "bytes" : "unsafe", elemType},
      {makeMapVars(1, bytes ? getBvTypeName(8) : getIntTypeName(8)).front(),
       makePtrVars(1).front(), elemBinding},
      getMapTypeName(bytes ? getBvTypeName(8) : getIntTypeName(8)), body);
}

// declare extractvalue functions
// e.g., function $extractvalue.float(p: ref, i: int) returns (float);
FuncDecl *extractValue(std::string resType) {
  std::list<Binding> args = makePtrVars(1);
  args.emplace_back(Binding{"i", "int"});
  return uninterpretedOp("$extractvalue", {resType}, args, resType);
}

// declare extractvalue functions for integers
// e.g., function $extractvalue.bv256(p: ref, i: int) returns (bv256);
FuncDecl *extractValue(unsigned width) {
  std::string resType =
      SmackOptions::BitPrecise ? getBvTypeName(width) : getIntTypeName(width);
  return extractValue(resType);
}

void printFuncs(FuncsT funcs, std::stringstream &s) {
  for (auto &f : funcs)
    if (f)
      s << f << "\n";
}

void describe(std::string comment, std::stringstream &s) {
  s << "// " << comment << "\n";
}

// generate bv arithmetic attribute
const Attr *IntOp::bvAttrFunc(std::string opName) {
  return makeBvbuiltinAttr("bv" + opName);
}

// generate int arithmetic attribute
const Attr *IntOp::intAttrFunc(std::string opName) {
  return makeBuiltinAttr(opName.substr(1));
}

struct IntOpGen::IntArithOp : public IntOp {
  IntArithOp(std::string opName, unsigned arity, Op *intOp, Op *bvOp,
             bool alsoUsedByPtr)
      : IntOp(opName, arity, intOp, bvOp, alsoUsedByPtr) {}

  FuncDecl *getIntFunc(unsigned size) const {
    if (!intOp)
      return nullptr;

    std::string type = getIntTypeName(size);
    std::string name = "$" + opName;

    if (auto bop = dyn_cast<BuiltinOp<IntOp::attrT>>(intOp))
      // builtin int functions
      // e.g.: function {:builtin "div"} $sdiv.i1(i1: i1, i2: i1) returns (i1);
      // return builtinOp(name, makeBuiltinAttr(op.substr(1)), {type},
      return builtinOp(name, ((IntOp::attrT)bop->func)(opName), {type},
                       makeIntVars(arity, type), type);
    else if (auto iop = dyn_cast<InlinedOp<IntOp::exprT>>(intOp))
      // inlined int functions
      // e.g.: function {:inline} $add.i1(i1: i1, i2: i1) returns (i1) { (i1 +
      // i2) }
      return inlinedOp(name, {type}, makeIntVars(arity, type), type,
                       ((IntOp::exprT)iop->func)(size));
    else
      // uninterpreted int functions
      // e.g.: function $not.i1(i1: i1) returns (i1);
      return uninterpretedOp(name, {type}, makeIntVars(arity, type), type);
  }

  FuncDecl *getBvFunc(unsigned size) const {
    if (!bvOp)
      return nullptr;

    std::string type = getBvTypeName(size);
    std::string name = "$" + opName;

    if (auto bop = dyn_cast<BuiltinOp<IntOp::attrT>>(bvOp))
      // builtin bv functions
      // e.g.: function {:bvbuiltin "bvadd"} $add.bv1(i1: bv1, i2: bv1) returns
      // (bv1);
      // return builtinOp(name, makeBvbuiltinAttr("bv"+op), {type},
      return builtinOp(name, ((IntOp::attrT)bop->func)(opName), {type},
                       makeIntVars(arity, type), type);
    else if (auto iop = dyn_cast<InlinedOp<IntOp::exprT>>(bvOp))
      // inlined bv functions
      // e.g.: function {:inline} $smin.bv32(i1: bv32, i2: bv32) returns (bv32)
      // { if $slt.bv32.bool(i1, i2) then i1 else i2 }
      return inlinedOp(name, {type}, makeIntVars(arity, type), type,
                       ((IntOp::exprT)iop->func)(size));
    else
      llvm_unreachable("no uninterpreted bv arithmetic operations.");
  }

  FuncsT getFuncs(unsigned size) const override {
    FuncsT funcs;
    if (!SmackOptions::BitPrecise ||
        (!SmackOptions::BitPrecisePointers && alsoUsedByPtr))
      funcs.push_back(getIntFunc(size));
    if (SmackOptions::BitPrecise ||
        (SmackOptions::BitPrecisePointers && alsoUsedByPtr))
      funcs.push_back(getBvFunc(size));
    return funcs;
  }

  // generate inlined int arithmetic function body such as `i1+i2`
  template <BinExpr::Binary OP> static const Expr *intArithExpr(unsigned size) {
    return new BinExpr(OP, makeIntVarExpr(1), makeIntVarExpr(2));
  }

  // generate inlined bv min/max function body such as
  // `if $slt.bv1.bool(i1, i2) then i1 else i2`
  template <bool SIGN, bool MIN>
  static const Expr *bvMinMaxExpr(unsigned size) {
    std::string signLetter = SIGN ? "s" : "u";
    std::string pred = MIN ? "lt" : "gt";
    return Expr::ifThenElse(
        Expr::fn(indexedName("$" + signLetter + pred,
                             {getBvTypeName(size), Naming::BOOL_TYPE}),
                 makeIntVarExprs(2)),
        makeIntVarExpr(1), makeIntVarExpr(2));
  }

  // generate inlined int min/max function body such as `if (i1 < i2) then i1
  // else i2`
  template <bool MIN, bool SIGN>
  static const Expr *intMinMaxExpr(unsigned size) {
    const Expr *a1 = makeIntVarExpr(1);
    const Expr *a2 = makeIntVarExpr(2);
    std::string predName =
        std::string("$") + (SIGN ? "s" : "u") + (MIN ? "lt" : "gt");
    auto pred = Expr::fn(
        indexedName(predName, {getIntTypeName(size), Naming::BOOL_TYPE}), a1,
        a2);
    return Expr::ifThenElse(pred, a1, a2);
  }

  // generate inlined `srem(i1, i2)` function body like
  // if (mod(i1,i2) != 0 && i1 < 0)
  // then mod(i1,i2) - abs(i2) else mod(i1,i2), where
  // `i1` is the dividend and `i2` is the divisor
  // `mod` is the Euclidean function defined in the SMT lib
  // therefore its result is always positive
  // the `srem` operation defined by LLVM follows the same
  // definition as modern C standards
  // (https://en.wikipedia.org/wiki/Modulo_operation#In_programming_languages)
  // its result has the same sign as i1 because the division rounds to 0
  // therefore, the only case `mod` and `srem` differ is when i1 is negative
  // and the remainder is not 0
  // for this case, the result of `srem` is the result of `mod` minus |i2|
  static const Expr *sremExpr(unsigned size) {
    std::string type = getIntTypeName(size);
    const Expr *dividend =
        IntOpGen::IntArithOp::wrappedExpr(size, makeIntVarExpr(1), false);
    const Expr *divisor =
        IntOpGen::IntArithOp::wrappedExpr(size, makeIntVarExpr(2), false);
    const Expr *zero = Expr::lit((unsigned long long)0);
    const Expr *mod = Expr::fn(indexedName("$smod", {type}), dividend, divisor);
    const Expr *modNeZero =
        Expr::fn(indexedName("$ne", {type, "bool"}), mod, zero);
    const Expr *dividendLtZero =
        Expr::fn(indexedName("$slt", {type, "bool"}), dividend, zero);
    const Expr *negRemainder = Expr::fn(
        indexedName("$sub", {type}), mod,
        Expr::fn(indexedName("$smax", {type}), divisor,
                 Expr::fn(indexedName("$sub", {type}), zero, divisor)));
    return Expr::ifThenElse(Expr::and_(modNeZero, dividendLtZero), negRemainder,
                            mod);
  }

  // generate inlined `urem` function body like
  // $smod.i32(i1,i2), where `$smod` is a wrapper to SMT's `mod` function
  static const Expr *uremExpr(unsigned size) {
    const Expr *dividend =
        IntOpGen::IntArithOp::wrappedExpr(size, makeIntVarExpr(1), true);
    const Expr *divisor =
        IntOpGen::IntArithOp::wrappedExpr(size, makeIntVarExpr(2), true);
    return Expr::fn(indexedName("$smod", {getIntTypeName(size)}), dividend,
                    divisor);
  }

  // generate inlined `tos` function body like
  // `if i >= -128 && i < 128 then i else $smod(i + 128, 256) - 128`
  static const Expr *tosExpr(unsigned size) {
    auto i = makeIntVarExpr(0);
    auto limitMinusOne = Expr::lit(getIntLimit(size - 1), 0);
    auto c = Expr::and_(
        new BinExpr(BinExpr::Gte, i, Expr::lit("-" + getIntLimit(size - 1), 0)),
        new BinExpr(BinExpr::Lt, i, limitMinusOne));
    auto type = getIntTypeName(size);
    return Expr::ifThenElse(
        c, i,
        Expr::fn(
            indexedName("$sub", {type}),
            Expr::fn(indexedName("$smod", {type}),
                     Expr::fn(indexedName("$add", {type}), i, limitMinusOne),
                     Expr::lit(getIntLimit(size), 0)),
            limitMinusOne));
  }

  // generate inlined `tou` function body like
  // `if i >= 0 && i < 256 then i else $smod.i8(i, 256)`
  static const Expr *touExpr(unsigned size) {
    auto i = makeIntVarExpr(0);
    auto limit = Expr::lit(getIntLimit(size), 0);
    auto c = Expr::and_(new BinExpr(BinExpr::Gte, i, Expr::lit(0ULL)),
                        new BinExpr(BinExpr::Lt, i, limit));
    auto type = getIntTypeName(size);
    return Expr::ifThenElse(c, i,
                            Expr::fn(indexedName("$smod", {type}), i, limit));
  }

  static const Expr *wrappedExpr(unsigned size, const Expr *e,
                                 bool isUnsigned) {
    return SmackOptions::WrappedIntegerEncoding
               ? Expr::fn(indexedName(Naming::getIntWrapFunc(isUnsigned),
                                      {getIntTypeName(size)}),
                          e)
               : e;
  }
  template <bool SIGN> static const Expr *divExpr(unsigned size) {
    const Expr *a1 = wrappedExpr(size, makeIntVarExpr(1), !SIGN);
    const Expr *a2 = wrappedExpr(size, makeIntVarExpr(2), !SIGN);
    return Expr::fn(indexedName("$idiv", {getIntTypeName(size)}), a1, a2);
  }
};

void IntOpGen::generateArithOps(std::stringstream &s) const {
  describe("Integer arithmetic operations", s);

  const auto bvBuiltinOp = new BuiltinOp<IntOp::attrT>(IntOp::bvAttrFunc);
  const auto intBuiltinOp = new BuiltinOp<IntOp::attrT>(IntOp::intAttrFunc);
  const auto uninterpretedOp = new UninterpretedOp();
  const std::vector<IntOpGen::IntArithOp> intArithOpTable{
      {"add", 2,
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::intArithExpr<BinExpr::Plus>),
       bvBuiltinOp, true},
      {"sub", 2,
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::intArithExpr<BinExpr::Minus>),
       bvBuiltinOp, true},
      {"mul", 2,
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::intArithExpr<BinExpr::Times>),
       bvBuiltinOp, true},
      {"idiv", 2, intBuiltinOp, bvBuiltinOp, false},
      {"sdiv", 2,
       new InlinedOp<IntOp::exprT>(IntOpGen::IntArithOp::divExpr<true>),
       bvBuiltinOp, false},
      {"udiv", 2,
       new InlinedOp<IntOp::exprT>(IntOpGen::IntArithOp::divExpr<false>),
       bvBuiltinOp, false},
      {"smod", 2, intBuiltinOp, bvBuiltinOp, false},
      {"srem", 2, new InlinedOp<IntOp::exprT>(IntOpGen::IntArithOp::sremExpr),
       bvBuiltinOp, false},
      {"urem", 2, new InlinedOp<IntOp::exprT>(IntOpGen::IntArithOp::uremExpr),
       bvBuiltinOp, false},
      {"shl", 2, uninterpretedOp, bvBuiltinOp, false},
      {"lshr", 2, uninterpretedOp, bvBuiltinOp, false},
      {"ashr", 2, uninterpretedOp, bvBuiltinOp, false},
      {"and", 2, uninterpretedOp, bvBuiltinOp, false},
      {"or", 2, uninterpretedOp, bvBuiltinOp, false},
      {"xor", 2, uninterpretedOp, bvBuiltinOp, false},
      {"nand", 2, uninterpretedOp, bvBuiltinOp, false},
      {"not", 1, uninterpretedOp, bvBuiltinOp, false},
      {"tos", 1,
       SmackOptions::WrappedIntegerEncoding
           ? new InlinedOp<IntOp::exprT>(IntOpGen::IntArithOp::tosExpr)
           : nullptr,
       nullptr, true},
      {"tou", 1,
       SmackOptions::WrappedIntegerEncoding
           ? new InlinedOp<IntOp::exprT>(IntOpGen::IntArithOp::touExpr)
           : nullptr,
       nullptr, true},
      {"smin", 2,
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::intMinMaxExpr<true, true>),
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::bvMinMaxExpr<true, true>),
       false},
      {"smax", 2,
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::intMinMaxExpr<false, true>),
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::bvMinMaxExpr<true, false>),
       false},
      {"umin", 2,
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::intMinMaxExpr<true, false>),
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::bvMinMaxExpr<false, true>),
       false},
      {"umax", 2,
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::intMinMaxExpr<false, false>),
       new InlinedOp<IntOp::exprT>(
           IntOpGen::IntArithOp::bvMinMaxExpr<false, false>),
       false}};

  for (auto &op : intArithOpTable)
    for (auto size : INTEGER_SIZES)
      printFuncs(op.getFuncs(size), s);

  if (!SmackOptions::BitPrecise) {
    // axioms for i1
    // e.g., axiom ($and.i1(0, 0) == 0);
    for (unsigned i = 0; i < 2; ++i) {
      for (unsigned j = 0; j < 2; ++j) {
        s << Decl::axiom(
                 Expr::eq(Expr::fn(indexedName("$and", {getIntTypeName(1)}),
                                   Expr::lit(i), Expr::lit(j)),
                          Expr::lit(i & j)))
          << "\n";
        s << Decl::axiom(
                 Expr::eq(Expr::fn(indexedName("$or", {getIntTypeName(1)}),
                                   Expr::lit(i), Expr::lit(j)),
                          Expr::lit(i | j)))
          << "\n";
        s << Decl::axiom(
                 Expr::eq(Expr::fn(indexedName("$xor", {getIntTypeName(1)}),
                                   Expr::lit(i), Expr::lit(j)),
                          Expr::lit(i ^ j)))
          << "\n";
      }
    }
    // special axiom for $and.i32: axiom ($and.i32(32, 16) == 0);
    s << Decl::axiom(
             Expr::eq(Expr::fn(indexedName("$and", {getIntTypeName(32)}),
                               Expr::lit(32U), Expr::lit(16U)),
                      Expr::lit(0U)))
      << "\n";
  }
}

struct IntOpGen::IntPred : public IntOp {

  IntPred(std::string opName, Op *intOp, Op *bvOp)
      : IntOp(opName, 2, intOp, bvOp, true) {}

  std::pair<FuncDecl *, FuncDecl *> getIntFuncs(unsigned size) const {
    std::string name = "$" + opName;
    std::string type = getIntTypeName(size);
    assert(isa<InlinedOp<IntOp::exprT>>(intOp));
    auto iop = llvm::cast<InlinedOp<IntOp::exprT>>(intOp);
    // e.g.: function {:inline} $ule.i1.bool(i1: i1, i2: i1) returns (bool)
    //        { (i1 <= i2) }
    auto compFunc =
        inlinedOp(name, {type, Naming::BOOL_TYPE}, makeIntVars(2, type),
                  Naming::BOOL_TYPE, ((IntOp::exprT)iop->func)(size));
    // e.g.: function {:inline} $ule.i1(i1: i1, i2: i1) returns (i1)
    //        { if $ule.i1.bool(i1, i2) then 1 else 0 }
    auto predFunc = inlinedOp(
        name, {type}, makeIntVars(2, type), getIntTypeName(1),
        Expr::ifThenElse(Expr::fn(indexedName(name, {type, Naming::BOOL_TYPE}),
                                  makeIntVarExprs(2)),
                         Expr::lit(1ll), Expr::lit(0ll)));
    return {compFunc, predFunc};
  }

  std::pair<FuncDecl *, FuncDecl *> getBvFuncs(unsigned size) const {
    std::string name = "$" + opName;
    std::string type = getBvTypeName(size);
    FuncDecl *compFunc, *predFunc;
    if (auto bop = dyn_cast<BuiltinOp<IntOp::attrT>>(bvOp))
      // e.g.: function {:bvbuiltin "bvule"} $ule.bv1.bool(i1: bv1, i2: bv1)
      //        returns (bool);
      compFunc = builtinOp(name, ((IntOp::attrT)bop->func)(opName),
                           {type, Naming::BOOL_TYPE}, makeIntVars(2, type),
                           Naming::BOOL_TYPE);
    else if (auto iop = dyn_cast<InlinedOp<IntOp::exprT>>(bvOp))
      // e.g.: function {:inline} $eq.bv1.bool(i1: bv1, i2: bv1) returns (bool)
      //        { (i1 == i2) }
      compFunc =
          inlinedOp(name, {type, Naming::BOOL_TYPE}, makeIntVars(2, type),
                    Naming::BOOL_TYPE, ((IntOp::exprT)iop->func)(size));
    else
      llvm_unreachable("no uninterpreted bv predicates");
    // e.g.: function {:inline} $ule.bv1(i1: bv1, i2: bv1) returns (bv1)
    //        { if $ule.bv1.bool(i1, i2) then 1bv1 else 0bv1 }
    predFunc = inlinedOp(
        name, {type}, makeIntVars(2, type), getBvTypeName(1),
        Expr::ifThenElse(Expr::fn(indexedName(name, {type, Naming::BOOL_TYPE}),
                                  makeIntVarExpr(1), makeIntVarExpr(2)),
                         Expr::lit(1, 1), Expr::lit(0, 1)));
    return {compFunc, predFunc};
  }

  FuncsT getFuncs(unsigned size) const override {
    FuncDecl *compFunc, *predFunc;
    FuncsT funcs;
    if (!SmackOptions::BitPrecise || !SmackOptions::BitPrecisePointers) {
      std::tie(compFunc, predFunc) = getIntFuncs(size);
      funcs.push_back(compFunc);
      funcs.push_back(predFunc);
    }
    if (SmackOptions::BitPrecise || SmackOptions::BitPrecisePointers) {
      std::tie(compFunc, predFunc) = getBvFuncs(size);
      funcs.push_back(compFunc);
      funcs.push_back(predFunc);
    }
    return funcs;
  }

  template <BinExpr::Binary OP, bool SIGN>
  static const Expr *intPredExpr(unsigned size) {
    // SHAOBO: we apply modulo operations to the operands.
    // Here is the reasoning: let's assume the cmp operation is unsigned,
    // and there's a sequence of arithmetic operations which only contain
    // addition, subtraction, multiplication. The inputs to such a computation
    // f is from i_1 to i_n. The hypothesis we want to prove here is
    // f(i_1,...,i_n) % B = f'(i_1 % B,...,i_n % B) where f' is the two's
    // complement counterpart of f, and B is 2^m where m is the bitwidth of the
    // operands. For certain operation o, its two's complement counterpart o' is
    // equivalent to o(i_1,i_2) % B. The axioms we used for the proof is as
    // follows, (X%B + Y%B)%B = (X+Y)%B, (X%B - Y%B)%B = (X-Y)%B,
    // (X%B * Y%B)%B = (X*Y)%B.
    // https://www.khanacademy.org/computing/computer-science/cryptography/modarithmetic/a/modular-addition-and-subtraction
    // https://www.khanacademy.org/computing/computer-science/cryptography/modarithmetic/a/modular-multiplication
    // so let's prove it inductively, for a computation f and its two
    // subcomputation, f_1 and f_2 connected by o, by definition, we have,
    // f(i_1,...,i_n) = o(f_1(i_1,...,i_n), f_2(i_1,...,i_n))
    // then, f(i_1,...,i_n)%B = o(f_1(i_1,...,i_n), f_2(i_1,...,i_n))%B
    // following the axioms, we have,
    // f(i_1,...,i_n)%B = o(f_1(i_1,...,i_n)%B, f_2(i_1,...,i_n)%B)%B
    // by the definition of two's complement arithmetic,
    // o(f_1(i_1,...,i_n)%B, f_2(i_1,...,i_n)%B)%B =
    // 	o'(f_1(i_1,...,i_n)%B, f_2(i_1,...,i_n)%B)
    // by induction, f_i(i_1,...,i_n)%B = f'_i(i_1%B,...,i_n%B)
    // therefore, o'(f_1(i_1,...,i_n)%B, f_2(i_1,...,i_n)%B) =
    // 	o'(f'_1(i_1%B,...,i_n%B), f_2'(i_1%B,...,i_n%B))
    // the rhs is exactly f' therefore we complete the proof.
    //
    // For signed comparison, the proof is trivial since we can get the precise
    // two's complement representation following the proof above.
    return new BinExpr(
        OP, IntOpGen::IntArithOp::wrappedExpr(size, makeIntVarExpr(1), !SIGN),
        IntOpGen::IntArithOp::wrappedExpr(size, makeIntVarExpr(2), !SIGN));
  }
};

void IntOpGen::generatePreds(std::stringstream &s) const {
  describe("Integer predicates", s);

  const auto bvBuiltinOp = new BuiltinOp<IntOp::attrT>(IntOp::bvAttrFunc);
  const auto uleInlinedOp = new InlinedOp<IntOp::exprT>(
      IntOpGen::IntPred::intPredExpr<BinExpr::Lte, false>);
  const auto ultInlinedOp = new InlinedOp<IntOp::exprT>(
      IntOpGen::IntPred::intPredExpr<BinExpr::Lt, false>);
  const auto ugeInlinedOp = new InlinedOp<IntOp::exprT>(
      IntOpGen::IntPred::intPredExpr<BinExpr::Gte, false>);
  const auto ugtInlinedOp = new InlinedOp<IntOp::exprT>(
      IntOpGen::IntPred::intPredExpr<BinExpr::Gt, false>);
  const auto sleInlinedOp = new InlinedOp<IntOp::exprT>(
      IntOpGen::IntPred::intPredExpr<BinExpr::Lte, true>);
  const auto sltInlinedOp = new InlinedOp<IntOp::exprT>(
      IntOpGen::IntPred::intPredExpr<BinExpr::Lt, true>);
  const auto sgeInlinedOp = new InlinedOp<IntOp::exprT>(
      IntOpGen::IntPred::intPredExpr<BinExpr::Gte, true>);
  const auto sgtInlinedOp = new InlinedOp<IntOp::exprT>(
      IntOpGen::IntPred::intPredExpr<BinExpr::Gt, true>);
  // normalize operands into 2's complement
  const auto eqInlinedOp = new InlinedOp<IntOp::exprT>(
      IntOpGen::IntPred::intPredExpr<BinExpr::Eq, false>);
  const auto neInlinedOp = new InlinedOp<IntOp::exprT>(
      IntOpGen::IntPred::intPredExpr<BinExpr::Neq, false>);
  const std::vector<IntPred> intPredTable{
      {"ule", uleInlinedOp, bvBuiltinOp}, {"ult", ultInlinedOp, bvBuiltinOp},
      {"uge", ugeInlinedOp, bvBuiltinOp}, {"ugt", ugtInlinedOp, bvBuiltinOp},
      {"sle", sleInlinedOp, bvBuiltinOp}, {"slt", sltInlinedOp, bvBuiltinOp},
      {"sge", sgeInlinedOp, bvBuiltinOp}, {"sgt", sgtInlinedOp, bvBuiltinOp},
      {"eq", eqInlinedOp, eqInlinedOp},   {"ne", neInlinedOp, neInlinedOp}};

  for (auto &pred : intPredTable)
    for (auto size : INTEGER_SIZES)
      printFuncs(pred.getFuncs(size), s);
}

struct IntOpGen::IntConv {
  typedef const Attr *(*attrT)(unsigned, unsigned);
  typedef const Expr *(*castExprT)(unsigned, unsigned);
  typedef const Expr *(*truncExprT)(unsigned);
  std::string opName;
  bool upCast;
  Op *intOp;
  Op *bvOp;

  FuncDecl *getIntFunc(unsigned size1, unsigned size2) const {
    assert(isa<InlinedOp<castExprT>>(intOp));
    auto iop = llvm::cast<InlinedOp<castExprT>>(intOp);
    std::string type1 = getIntTypeName(size1);
    std::string type2 = getIntTypeName(size2);

    // e.g.: function {:inline} $zext.i1.i5(i: i1) returns (i5) { i }
    return inlinedOp("$" + opName, {type1, type2}, makeIntVars(1, type1), type2,
                     ((castExprT)iop->func)(size1, size2));
  }

  FuncDecl *getBvFunc(unsigned size1, unsigned size2) const {
    std::string type1 = getBvTypeName(size1);
    std::string type2 = getBvTypeName(size2);
    std::string name = "$" + opName;
    if (auto bop = dyn_cast<BuiltinOp<attrT>>(bvOp)) {
      // e.g.: function {:bvbuiltin (_ sign_extend 8)} $sext.bv8.bv16(i: bv8)
      // returns (bv16);
      return builtinOp(name, ((attrT)bop->func)(size1, size2), {type1, type2},
                       makeIntVars(1, type1), type2);
    } else if (auto iop = dyn_cast<InlinedOp<truncExprT>>(bvOp)) {
      // e.g.: function {:inline} $trunc.bv5.bv1(i: bv5) returns (bv1) { i[1:0]
      // }
      return inlinedOp(name, {type1, type2}, makeIntVars(1, type1), type2,
                       ((truncExprT)iop->func)(size2));
    } else
      llvm_unreachable("no uninterpreted bv cast");
  }

  FuncsT getFuncs(unsigned size1, unsigned size2) const {
    if (SmackOptions::BitPrecise)
      return {getBvFunc(size1, size2)};
    else
      return {getIntFunc(size1, size2)};
  }

  // generate identity expression such as `i1`
  static const Expr *intTruncExpr(unsigned size1, unsigned size2) {
    // SHAOBO: from Ben,
    // Let F be a computation with inputs i_1, ..., i_n and let T be a
    // truncation operation from 2^A to 2^B where A > B. We want show that the
    // truncation of a two's complement number with a bitwidth of A to a
    // bitwidth of B is equivalent to modding that number by the base 2^B. In
    // other words, we want to prove the hypothesis that
    //
    // T(F'(i_1 % 2^A, ..., i_n % 2^A)) = F(i_1, ..., i_n) % 2^B
    //
    // To do this, we use two equivalencies. First, notice that we proved
    // earlier that
    //
    // F'(i_1 % A, ..., i_n % A) = F(i_1, ..., i_n) % A
    //
    // Also, by definition,
    //
    // trunc_A->B(x) = x % B
    //
    // This means that
    //
    // T(F'(i_1 % 2^A, ..., i_n % 2^A)) = T(F(i_1, ..., i_n) % 2^A)
    //	                                = (F(i_1, ..., i_n) % 2^A) % 2^B
    //
    // Next notice that F(i_1, ..., i_n) % 2^A = F(i_1, ..., i_n) - c * 2^A by
    // definition for some integer c. Because of this, we can use the following
    // axiom of modularity to simplify it: (X%M - Y%M)%M = (X-Y)%M
    // https://www.khanacademy.org/computing/computer-science/cryptography/modarithmetic/a/modular-addition-and-subtraction
    //
    // (F(i_1, ..., i_n) - c * 2^A) % 2^B
    //    = ((F(i_1, ..., i_n) % 2^B) - (c * 2^A % 2^B)) % 2^B
    //
    // Since the second number is a multiple of 2^B, it goes to 0 and we're left
    // with
    //
    // (F(i_1, ..., i_n) % 2^B - 0) % 2^B = F(i_1, ..., i_n) % 2^B
    //
    // Therefore, T(F'(i_1 % 2^A, ..., i_n % 2^A)) = F(i_1, ..., i_n) % 2^B
    return IntOpGen::IntArithOp::wrappedExpr(size2, makeIntVarExpr(0), true);
  }

  template <bool SIGN>
  static const Expr *intExtExpr(unsigned size1, unsigned size2) {
    // SHAOBO: from Ben
    // Let F be a computation with inputs i_1, ..., i_n and let Z be an unsigned
    // extension operation from 2^A to 2^B where A < B. We want show that the
    // unsigned extension of a two's complement number with a bitwidth of A to a
    // bitwidth of B is equivalent to modding that number by the base 2^A. In
    // other words, we want to prove the hypothesis that
    //
    // Z(F'(i_1 % 2^A, ..., i_n % 2^A)) = F(i_1, ..., i_n) % 2^A
    //
    // To do this, we use two equivalencies. First, notice that we proved
    // earlier that
    //
    // F'(i_1 % A, ..., i_n % A) = F(i_1, ..., i_n) % A
    //
    // Also, by definition,
    //
    // zext_A->B(x) = x % A
    //
    // This means that
    //
    // Z(F'(i_1 % 2^A, ..., i_n % 2^A)) = Z(F(i_1, ..., i_n) % 2^A)
    //                                  = (F(i_1, ..., i_n) % 2^A) % 2^A
    //                                  = F(i_1, ..., i_n) % 2^A
    //
    // Therefore, Z(F'(i_1 % 2^A, ..., i_n % 2^A)) = F(i_1, ..., i_n) % 2^A
    //
    //
    // Let F be a computation with inputs i_1, ..., i_n and let S be a signed
    // extension operation from 2^A to 2^B where A < B. We want show that the
    // signed extension of a two's complement number with a bitwidth of A to a
    // bitwidth of B is equivalent to converting that number to unsigned,
    // modding the result by the base 2^A, and then converting back to signed.
    // In other words, we want to prove the hypothesis that
    //
    // S(F'(i_1 % 2^A, ..., i_n % 2^A) - 2^(A-1))
    //    = (F(i_1, ..., i_n) + 2^(A-1)) % 2^A - 2^(A-1)
    //
    // To do this, we use two equivalencies. First, notice that we proved
    // earlier that
    //
    // F'(i_1 % A, ..., i_n % A) = F(i_1, ..., i_n) % A
    //
    // Also, by definition,
    //
    // sext_A->B(x) = (x + 2^(A-1)) % 2^A - 2^(A-1)
    //
    // This means that
    //
    // S(F'(i_1 % 2^A, ..., i_n % 2^A)) = S(F(i_1, ..., i_n) % 2^A)
    //    = (F(i_1, ..., i_n) % 2^A + 2^(A-1)) % 2^A - 2^(A-1)
    //
    // Because 2^(A-1) < 2^A, 2^(A-1) % 2^A = 2^(A-1). Lets rewrite this using
    // that fact.
    //
    // (F(i_1, ..., i_n) % 2^A + 2^(A-1)) % 2^A - 2^(A-1)
    //	  = (F(i_1, ..., i_n) % 2^A + 2^(A-1) % 2^A) % 2^A - 2^(A-1)
    //
    // Next, we can use the following axiom of modularity to simplify it:
    // (X%M + Y%M)%M = (X+Y)%M
    // https://www.khanacademy.org/computing/computer-science/cryptography/modarithmetic/a/modular-addition-and-subtraction
    //
    // (F(i_1, ..., i_n) % 2^A + 2^(A-1) % 2^A) % 2^A - 2^(A-1)
    //	  = (F(i_1, ..., i_n) + 2^(A-1)) % 2^A - 2^(A-1)
    //
    // Therefore, S(F'(i_1 % 2^A, ..., i_n % 2^A) - 2^(A-1))
    //	  = (F(i_1, ..., i_n) + 2^(A-1)) % 2^A - 2^(A-1)
    return IntOpGen::IntArithOp::wrappedExpr(size1, makeIntVarExpr(0), !SIGN);
  }

  // generate bv truncation function body such as `i[1:0]`
  static const Expr *bvTruncExpr(unsigned size) {
    return Expr::bvExtract(makeIntVarName(0), size, 0);
  }

  // generate bv extension function attribute such as `:bvbuiltin (_ sign_extend
  // 8)`
  template <bool SIGN>
  static const Attr *extAttr(unsigned size1, unsigned size2) {
    std::string builtInOp = SIGN ? "sign_extend" : "zero_extend";
    std::string builtInAttrArg =
        "(_ " + builtInOp + " " + std::to_string(size2 - size1) + ")";
    return makeBvbuiltinAttr(builtInAttrArg);
  }
};

void IntOpGen::generateConvOps(std::stringstream &s) const {
  describe("Conversion between integer types", s);

  const auto intTrunc =
      new InlinedOp<IntConv::castExprT>(IntConv::intTruncExpr);
  const auto intSext =
      new InlinedOp<IntConv::castExprT>(IntConv::intExtExpr<true>);
  const auto intZext =
      new InlinedOp<IntConv::castExprT>(IntConv::intExtExpr<false>);
  const auto bvTrunc = new InlinedOp<IntConv::truncExprT>(IntConv::bvTruncExpr);
  const auto builtinSext =
      new BuiltinOp<IntConv::attrT>(IntConv::extAttr<true>);
  const auto builtinZext =
      new BuiltinOp<IntConv::attrT>(IntConv::extAttr<false>);
  const std::vector<IntConv> intConvTable{{"trunc", false, intTrunc, bvTrunc},
                                          {"sext", true, intSext, builtinSext},
                                          {"zext", true, intZext, builtinZext}};

  for (auto &conv : intConvTable) {
    for (size_t s1 = 0; s1 < INTEGER_SIZES.size(); ++s1) {
      const unsigned &size1 = INTEGER_SIZES[s1];
      for (size_t s2 = s1 + 1; s2 < INTEGER_SIZES.size(); ++s2) {
        const unsigned &size2 = INTEGER_SIZES[s2];
        if (conv.upCast)
          printFuncs(conv.getFuncs(size1, size2), s);
        else
          printFuncs(conv.getFuncs(size2, size1), s);
      }
    }
  }
}

void IntOpGen::generateMemOps(std::stringstream &s) const {
  describe("Integer load/store operations", s);

  for (auto size : INTEGER_SIZES) {
    if (!SmackOptions::BitPrecise) {
      std::string type = getIntTypeName(size);
      auto binding = makeIntVars(1, type).front();
      // e.g.: function {:inline} $load.i1(M: [ref] i1, p: ref) returns (i1) {
      // M[p] }
      s << prelude.safeLoad(type) << "\n";
      // e.g.: function {:inline} $store.i1(M: [ref] i1, p: ref, i: i1)
      //        returns ([ref] i1) { M[p := i] }
      s << prelude.safeStore(binding) << "\n";
    } else {
      // e.g.: function {:inline} $load.bv1(M: [ref] bv1, p: ref) returns (bv1)
      // { M[p] }
      std::string type = getBvTypeName(size);
      auto binding = makeIntVars(1, type).front();
      s << prelude.safeLoad(type) << "\n";
      // e.g.: function {:inline} $store.bv1(M: [ref] bv1, p: ref, v: bv1)
      //        returns ([ref] bv1) { M[p := i] }
      s << prelude.safeStore(binding) << "\n";

      auto byteType = getBvTypeName(8);
      auto valExpr = makeIntVarExpr(0);

      if (size < 8) {
        // e.g., function {:inline} $load.bytes.bv1(M: [ref] bv8, p: ref)
        // returns (bv1) { $trunc.bv8.bv1(M[p]) }
        s << prelude.unsafeLoad(
                 type, Expr::fn(indexedName("$trunc", {byteType, type}),
                                prelude.mapSelExpr(0)))
          << "\n";
        // e.g., function {:inline} $store.bytes.bv1(M: [ref] bv8, p: ref, i:
        // bv1)
        // returns ([ref] bv8) { M[p := $zext.bv1.bv8(i)] }
        s << prelude.unsafeStore(
                 binding,
                 prelude.mapUpdExpr(
                     0,
                     Expr::fn(indexedName("$zext", {type, byteType}), valExpr)))
          << "\n";
      } else if (size == 8) {
        // function {:inline} $load.bytes.bv8(M: [ref] bv8, p: ref) returns
        // (bv8) { M[p] }
        s << prelude.unsafeLoad(type, prelude.mapSelExpr(0)) << "\n";
        // function {:inline} $load.bytes.bv8(M: [ref] bv8, p: ref) returns
        // (bv8) { M[p] }
        s << prelude.unsafeStore(binding, prelude.mapUpdExpr(0, valExpr))
          << "\n";
      } else {
        auto loadBody = prelude.mapSelExpr(0);
        auto storeBody = prelude.mapUpdExpr(0, Expr::bvExtract(valExpr, 8, 0));
        for (unsigned i = 1; i < (size >> 3); ++i) {
          unsigned lowerIdx = i << 3;
          unsigned upperIdx = lowerIdx + 8;
          loadBody = Expr::bvConcat(prelude.mapSelExpr(i), loadBody);
          storeBody = prelude.mapUpdExpr(
              i, Expr::bvExtract(valExpr, upperIdx, lowerIdx), storeBody);
        }
        // e.g., function {:inline} $load.bytes.bv16(M: [ref] bv8, p: ref)
        // returns (bv16) { (M[$add.ref(p, 1)]++M[p]) }
        s << prelude.unsafeLoad(type, loadBody) << "\n";
        // e.g., function {:inline} $store.bytes.bv16(M: [ref] bv8, p: ref, i:
        // bv16)
        // returns ([ref] bv8) { M[p := i[8:0]][$add.ref(p, 1) := i[16:8]] }
        s << prelude.unsafeStore(binding, storeBody) << "\n";
      }
    }
  }
}

void IntOpGen::generateExtractValueFuncs(std::stringstream &s) const {
  for (auto size : INTEGER_SIZES)
    s << extractValue(size) << "\n";
}

void IntOpGen::generateBvIntConvs(std::stringstream &s) const {
  describe("SMT bit-vector/integer conversion", s);

  auto ptrSize = prelude.rep.ptrSizeInBits;
  std::string b = std::to_string(ptrSize);
  std::string bt = "bv" + b;
  std::string it = "i" + b;
  s << Decl::function(indexedName("$int2bv", {ptrSize}), {{"i", it}}, bt,
                      nullptr, {makeBuiltinAttr("(_ int2bv " + b + ")")})
    << "\n";
  if (SmackOptions::BitPrecise && !SmackOptions::BitPrecisePointers) {
    s << Decl::function(indexedName("$bv2uint", {ptrSize}), {{"i", bt}}, it,
                        nullptr, {makeBuiltinAttr("bv2nat")})
      << "\n";
    const Expr *arg = Expr::id("i");
    const Expr *uint = Expr::fn(indexedName("$bv2uint", {ptrSize}), arg);
    std::string offset;
    if (ptrSize == 32)
      offset = "4294967296";
    else if (ptrSize == 64)
      offset = "18446744073709551616";
    else
      llvm_unreachable("Unexpected pointer bit width.");
    s << Decl::function(
             indexedName("$bv2int", {ptrSize}), {{"i", bt}}, it,
             Expr::ifThenElse(
                 Expr::fn(indexedName("$slt", {bt, Naming::BOOL_TYPE}),
                          {arg, Expr::lit(0ULL, ptrSize)}),
                 Expr::fn(indexedName("$sub", {it}),
                          {uint, Expr::lit(offset, 0U)}),
                 uint),
             {makeInlineAttr()})
      << "\n";
  } else
    s << Decl::function(indexedName("$bv2int", {ptrSize}), {{"i", bt}}, it,
                        nullptr, {makeBuiltinAttr("bv2nat")})
      << "\n";
  s << "\n";
}

void IntOpGen::generate(std::stringstream &s) const {
  generateBvIntConvs(s);
  generateArithOps(s);
  generatePreds(s);
  generateMemOps(s);
  generateConvOps(s);
  generateExtractValueFuncs(s);
}

void TypeDeclGen::generate(std::stringstream &s) const {
  describe("Basic types", s);

  for (unsigned size : IntOpGen::INTEGER_SIZES)
    s << Decl::typee(getIntTypeName(size), "int") << "\n";
  s << Decl::typee(Naming::PTR_TYPE, prelude.rep.pointerType()) << "\n";
  if (SmackOptions::FloatEnabled) {
    s << Decl::typee(Naming::HALF_TYPE, "float11e5") << "\n";
    s << Decl::typee(Naming::FLOAT_TYPE, "float24e8") << "\n";
    s << Decl::typee(Naming::DOUBLE_TYPE, "float53e11") << "\n";
    s << Decl::typee(Naming::LONG_DOUBLE_TYPE, "float65e15") << "\n";
  } else {
    s << Decl::typee(Naming::UNINTERPRETED_FLOAT_TYPE, "") << "\n";
  }
  s << "\n";
}

void ConstDeclGen::generatePtrConstant(unsigned val,
                                       std::stringstream &s) const {
  std::string ptrConst =
      indexedName("$" + std::to_string(val), {Naming::PTR_TYPE});
  s << Decl::constant(ptrConst, Naming::PTR_TYPE) << "\n";
  s << Decl::axiom(Expr::eq(Expr::id(ptrConst),
                            prelude.rep.pointerLit((unsigned long long)val)))
    << "\n";
}

void ConstDeclGen::generateIntConstant(unsigned val,
                                       std::stringstream &s) const {
  std::string intConst = "$" + std::to_string(val);
  s << Decl::constant(intConst, prelude.rep.intType(32)) << "\n";
  s << Decl::axiom(
           Expr::eq(Expr::id(intConst),
                    prelude.rep.integerLit((unsigned long long)val, 32)))
    << "\n";
}

void ConstDeclGen::generate(std::stringstream &s) const {
  describe("Basic constants", s);

  // e.g., const $0: i32; axiom ($0 == 0);
  generateIntConstant(0, s);
  generateIntConstant(1, s);

  // e.g., const $1.ref: ref; axiom ($1.ref == 1);
  generatePtrConstant(0, s);
  generatePtrConstant(1, s);
  generatePtrConstant(1024, s);

  describe("Memory model constants", s);

  // e.g., const $GLOBALS_BOTTOM: ref;
  s << Decl::constant(Naming::GLOBALS_BOTTOM, Naming::PTR_TYPE) << "\n";
  s << Decl::constant(Naming::EXTERNS_BOTTOM, Naming::PTR_TYPE) << "\n";
  s << Decl::constant(Naming::MALLOC_TOP, Naming::PTR_TYPE) << "\n";
  s << "\n";
}

void MemDeclGen::generateMemoryMaps(std::stringstream &s) const {
  describe("Memory maps (" + std::to_string(prelude.rep.regions->size()) +
               " regions)",
           s);

  for (auto M : prelude.rep.memoryMaps())
    s << "var " << M.first << ": " << M.second << ";"
      << "\n";

  s << "\n";
}

void MemDeclGen::generateAddrBoundsAndPred(std::stringstream &s) const {
  describe("Memory address bounds", s);

  // e.g., axiom ($GLOBALS_BOTTOM == $sub.ref(0, 45419));
  s << Decl::axiom(Expr::eq(Expr::id(Naming::GLOBALS_BOTTOM),
                            prelude.rep.pointerLit(prelude.rep.globalsOffset)))
    << "\n";
  s << Decl::axiom(Expr::eq(
           Expr::id(Naming::EXTERNS_BOTTOM),
           Expr::fn("$add.ref", Expr::id(Naming::GLOBALS_BOTTOM),
                    prelude.rep.pointerLit(prelude.rep.externsOffset))))
    << "\n";
  unsigned long long malloc_top;
  if (prelude.rep.ptrSizeInBits == 32)
    malloc_top = 2147483647UL;
  else if (prelude.rep.ptrSizeInBits == 64)
    malloc_top = 9223372036854775807UL;
  else
    llvm_unreachable("Unexpected pointer bit width.");
  s << Decl::axiom(Expr::eq(Expr::id(Naming::MALLOC_TOP),
                            prelude.rep.pointerLit(malloc_top)))
    << "\n";

  // $isExternal predicate:
  // function {:inline} $isExternal(p: ref) returns (bool)
  // {$slt.ref.bool(p,$EXTERNS_BOTTOM)}
  s << Decl::function(
           Naming::EXTERNAL_ADDR, makePtrVars(1), Naming::BOOL_TYPE,
           Expr::fn(indexedName("$slt", {Naming::PTR_TYPE, Naming::BOOL_TYPE}),
                    makePtrVarExpr(0), Expr::id(Naming::EXTERNS_BOTTOM)),
           {makeInlineAttr()})
    << "\n";
  s << "\n";
}

void MemDeclGen::generateGlobalAllocations(std::stringstream &s) const {
  if (SmackOptions::MemorySafety) {
    describe("Global allocations", s);

    std::list<const Stmt *> stmts;
    for (auto E : prelude.rep.globalAllocations)
      stmts.push_back(
          Stmt::call("$galloc", {prelude.rep.expr(E.first),
                                 prelude.rep.pointerLit(E.second)}));
    s << Decl::procedure("$global_allocations", {}, {}, {},
                         {Block::block("", stmts)})
      << "\n";
    s << "\n";
  }
}

void MemDeclGen::generate(std::stringstream &s) const {
  generateMemoryMaps(s);
  generateAddrBoundsAndPred(s);
  generateGlobalAllocations(s);
}

void PtrOpGen::generatePtrNumConvs(std::stringstream &s) const {
  describe("Pointer-number conversion", s);

  // e.g., function {:inline} $p2i.ref.i8(p: ref) returns (i8) {
  // $trunc.i64.i8(p) }
  for (unsigned i = 8; i <= 64; i <<= 1) {
    s << Decl::function(
             indexedName("$p2i", {Naming::PTR_TYPE, prelude.rep.intType(i)}),
             {{"p", Naming::PTR_TYPE}}, prelude.rep.intType(i),
             prelude.rep.pointerToInteger(Expr::id("p"), i), {makeInlineAttr()})
      << "\n";
    s << Decl::function(
             indexedName("$i2p", {prelude.rep.intType(i), Naming::PTR_TYPE}),
             {{"i", prelude.rep.intType(i)}}, Naming::PTR_TYPE,
             prelude.rep.integerToPointer(Expr::id("i"), i), {makeInlineAttr()})
      << "\n";
  }
  s << "\n";
}

void PtrOpGen::generatePreds(std::stringstream &s) const {
  describe("Pointer predicates", s);

  using PredInfo = std::pair<std::string, BinExpr::Binary>;
  const std::vector<PredInfo> predicates{
      {"$eq", BinExpr::Eq},   {"$ne", BinExpr::Neq},  {"$ugt", BinExpr::Gt},
      {"$uge", BinExpr::Gte}, {"$ult", BinExpr::Lt},  {"$ule", BinExpr::Lte},
      {"$sgt", BinExpr::Gt},  {"$sge", BinExpr::Gte}, {"$slt", BinExpr::Lt},
      {"$sle", BinExpr::Lte}};

  // e.g., function {:inline} $eq.ref(p1: ref, p2: ref)
  // returns (i1) { (if $eq.i64.bool(p1, p2) then 1 else 0) }
  for (auto info : predicates) {
    auto predName = info.first;
    auto binPred = info.second;
    auto condExpr = Expr::fn(
        indexedName(predName, {prelude.rep.pointerType(), Naming::BOOL_TYPE}),
        {makePtrVarExpr(1), makePtrVarExpr(2)});
    const Expr *predExpr =
        SmackOptions::BitPrecisePointers
            ? condExpr
            : new BinExpr(binPred, makePtrVarExpr(1), makePtrVarExpr(2));

    s << Decl::function(
             indexedName(predName, {Naming::PTR_TYPE, Naming::BOOL_TYPE}),
             {{"p1", Naming::PTR_TYPE}, {"p2", Naming::PTR_TYPE}},
             Naming::BOOL_TYPE, predExpr, {makeInlineAttr()})
      << "\n";

    s << Decl::function(indexedName(predName, {Naming::PTR_TYPE}),
                        {{"p1", Naming::PTR_TYPE}, {"p2", Naming::PTR_TYPE}},
                        prelude.rep.intType(1),
                        Expr::ifThenElse(
                            Expr::fn(indexedName(predName, {Naming::PTR_TYPE,
                                                            Naming::BOOL_TYPE}),
                                     {makePtrVarExpr(1), makePtrVarExpr(2)}),
                            prelude.rep.integerLit(1LL, 1),
                            prelude.rep.integerLit(0LL, 1)),
                        {makeInlineAttr()})
      << "\n";
  }
  s << "\n";
}

void PtrOpGen::generateArithOps(std::stringstream &s) const {
  describe("Pointer arithmetic operations", s);

  const std::vector<std::string> operations = {"$add", "$sub", "$mul"};

  // e.g., function {:inline} $add.ref(p1: ref, p2: ref) returns (ref) {
  // $add.i64(p1, p2) }
  for (auto op : operations) {
    s << Decl::function(indexedName(op, {Naming::PTR_TYPE}),
                        {{"p1", Naming::PTR_TYPE}, {"p2", Naming::PTR_TYPE}},
                        Naming::PTR_TYPE,
                        Expr::fn(indexedName(op, {prelude.rep.pointerType()}),
                                 {Expr::id("p1"), Expr::id("p2")}),
                        {makeInlineAttr()})
      << "\n";
  }
  s << "\n";
}

void PtrOpGen::generateMemOps(std::stringstream &s) const {
  describe("Pointer load/store operations", s);

  if (SmackOptions::BitPrecise) {
    describe("Bytewise pointer storage", s);

    // e.g., function {:inline} $load.bytes.ref(M: [ref] bv8, p: ref)
    // returns (ref) { $i2p.bv64.ref($load.bytes.bv64(M, p)) }
    auto intType = getBvTypeName(prelude.rep.ptrSizeInBits);
    s << prelude.unsafeLoad(
             Naming::PTR_TYPE,
             Expr::fn(indexedName("$i2p", {intType, Naming::PTR_TYPE}),
                      Expr::fn(indexedName("$load", {"bytes", intType}),
                               makeMapVarExpr(0), makePtrVarExpr(0))))
      << "\n";

    // e.g., function {:inline} $store.bytes.ref(M: [ref] bv8, p: ref, p1: ref)
    // returns ([ref] bv8) { $store.bytes.bv64(M, p, $p2i.ref.bv64(p1)) }
    auto binding = makePtrVars(2).front();
    auto indexExpr = makePtrVarExpr(0);
    s << prelude.unsafeStore(
             binding,
             Expr::fn(indexedName("$store", {"bytes", intType}),
                      makeMapVarExpr(0), indexExpr,
                      Expr::fn(indexedName("$p2i", {Naming::PTR_TYPE, intType}),
                               makePtrVarExpr(1))))
      << "\n";
  }
  s << prelude.safeLoad(Naming::PTR_TYPE) << "\n";
  s << prelude.safeStore(makeIntVars(1, Naming::PTR_TYPE).front()) << "\n";
  s << "\n";
}

void PtrOpGen::generateConvOps(std::stringstream &s) const {
  describe("Pointer conversion", s);

  // pointer bit casts:
  // function {:inline} $bitcast.ref.ref(i: ref) returns (ref) {i}
  s << inlinedOp("$bitcast", {Naming::PTR_TYPE, Naming::PTR_TYPE},
                 makePtrVars(1), Naming::PTR_TYPE, makePtrVarExpr(0))
    << "\n";
}

void PtrOpGen::generateExtractValueFuncs(std::stringstream &s) const {
  s << extractValue(Naming::PTR_TYPE) << "\n";
}

void PtrOpGen::generate(std::stringstream &s) const {
  generateArithOps(s);
  generatePreds(s);
  generateMemOps(s);
  generateConvOps(s);
  generateExtractValueFuncs(s);
  generatePtrNumConvs(s);
}

// generate floating-point built-in attributes
const Attr *FpOp::fpAttrFunc(std::string opName) {
  static const std::map<std::string, std::string> fpAttrTable{
      {"abs", "fp.abs"},
      {"round", "fp.roundToIntegral"},
      {"min", "fp.min"},
      {"max", "fp.max"},
      {"sqrt", "fp.sqrt"},
      {"fadd", "fp.add"},
      {"fsub", "fp.sub"},
      {"fmul", "fp.mul"},
      {"fdiv", "fp.div"},
      {"frem", "fp.rem"},
      {"fma", "fp.fma"},
      {"fneg", "fp.neg"},
      {"isnormal", "fp.isNormal"},
      {"issubnormal", "fp.isSubnormal"},
      {"iszero", "fp.isZero"},
      {"isinfinite", "fp.isInfinite"},
      {"isnan", "fp.isNaN"},
      {"isnegative", "fp.isNegative"},
      {"ispositive", "fp.isPositive"},
      {"foeq", "fp.eq"},
      {"fole", "fp.leq"},
      {"folt", "fp.lt"},
      {"foge", "fp.geq"},
      {"fogt", "fp.gt"}};
  return makeBuiltinAttr(fpAttrTable.at(opName));
}

struct FpOpGen::FpArithOp : public FpOp {
  bool rMode;

  FpArithOp(std::string opName, unsigned arity, bool rMode)
      : FpOp(opName, arity, new BuiltinOp<FpOp::attrT>(fpAttrFunc)),
        rMode(rMode) {}

  FuncDecl *getModeledFpFunc(unsigned bitWidth) const override {
    assert(isa<BuiltinOp<FpOp::attrT>>(op));
    auto bop = llvm::cast<BuiltinOp<FpOp::attrT>>(op);
    auto builtinAttr = ((FpOp::attrT)bop->func)(opName);
    auto type = getFpTypeName(bitWidth);
    auto name = "$" + opName;
    std::list<Binding> bs = makeFpVars(arity, bitWidth);

    if (rMode)
      bs.insert(bs.begin(), {makeRMODEVarName(), getRMODETypeName()});

    // e.g., function {:builtin "fp.add"} $fadd.bvhalf(rm: rmode, f1: bvhalf,
    // f2: bvhalf)
    // returns (bvhalf);
    return builtinOp(name, builtinAttr, {type}, bs, type);
  }

  FuncDecl *getUninterpretedFpFunc() const override {
    auto name = "$" + opName;
    std::string type = getFpTypeName(0);
    // e.g.: function $fadd.fp(f1: float, f2: float) returns (float);
    return uninterpretedOp(name, {type}, makeFpVars(arity, 0), type);
  }
};

void FpOpGen::generateArithOps(std::stringstream &s) const {
  describe("Floating-point arithmetic operations", s);

  // TODO eliminate the fourth item
  const std::vector<FpArithOp> fpArithOps{
      {"abs", 1, false}, {"round", 1, true}, {"sqrt", 1, true},
      {"fadd", 2, true}, {"fsub", 2, true},  {"fmul", 2, true},
      {"fdiv", 2, true}, {"frem", 2, false}, {"min", 2, false},
      {"max", 2, false}, {"fma", 3, true},   {"fneg", 1, false}};

  for (auto &f : fpArithOps) {
    if (SmackOptions::FloatEnabled)
      for (auto bw : FP_BIT_WIDTHS)
        s << f.getModeledFpFunc(bw) << "\n";
    else
      s << f.getUninterpretedFpFunc() << "\n";
  }
}

struct FpOpGen::FpPred : public FpOp {
  typedef const Expr *(*exprT)(std::string, const Expr *a1, const Expr *a2,
                               unsigned bitWidth);
  bool llvmBuiltin;

  FpPred(std::string opName, unsigned arity, bool llvmBuiltin, Op *op)
      : FpOp(opName, arity, op), llvmBuiltin(llvmBuiltin) {}

  FuncDecl *getModeledFpFunc(unsigned bitWidth) const override {
    auto type = getFpTypeName(bitWidth);
    auto name = "$" + opName;
    if (auto bop = dyn_cast<BuiltinOp<FpOp::attrT>>(op)) {
      auto builtinAttr = ((FpOp::attrT)bop->func)(opName);

      // e.g: function {:builtin "fp.isNormal"} $isnormal.bvhalf.bool(i: bvhalf)
      // returns (bool);
      return builtinOp(name, builtinAttr, {type, Naming::BOOL_TYPE},
                       makeFpVars(arity, bitWidth), Naming::BOOL_TYPE);
    } else if (auto iop = dyn_cast<InlinedOp<exprT>>(op)) {
      auto a1 = makeFpVarExpr(1);
      auto a2 = makeFpVarExpr(2);
      // e.g.:  function {:inline} $ford.bvhalf.bool(f1:bvhalf, f2:bvhalf)
      // returns (bool) {!$funo.bvhalf.bool(f1,f2)}
      return inlinedOp(name, {type, Naming::BOOL_TYPE},
                       makeFpVars(arity, bitWidth), Naming::BOOL_TYPE,
                       ((exprT)iop->func)(opName, a1, a2, bitWidth));
    } else
      llvm_unreachable("no uninterpreted fp predicates.");
  }

  FuncDecl *getUninterpretedFpFunc() const override {
    if (llvmBuiltin) {
      // e.g: function $foeq.float.bool(i1: float, i2: float) returns (bool);
      auto type = getFpTypeName(0);

      return uninterpretedOp("$" + opName, {type, Naming::BOOL_TYPE},
                             makeFpVars(arity, 0), Naming::BOOL_TYPE);
    } else
      return nullptr;
  }

  // helper function: generate expressions such as `$isnan.bvhalf.bool(f1)`
  static const Expr *applyCompFn(std::string baseName, unsigned bitWidth,
                                 std::list<const Expr *> args) {
    return Expr::fn(
        indexedName(baseName, {getFpTypeName(bitWidth), Naming::BOOL_TYPE}),
        args);
  }

  // helper function: generate expressions that negate a predicate such as
  // !($fueq.bvhalf.bool(f1, f2))
  static std::function<const Expr *(const Expr *, const Expr *, unsigned)>
  fpPredNegBody(std::string opName) {
    return [opName](const Expr *a1, const Expr *a2, unsigned bitWidth) {
      return Expr::not_(applyCompFn(opName, bitWidth, {a1, a2}));
    };
  }

  // e.g., ($isnan.bvhalf.bool(f1) || $isnan.bvhalf.bool(f2))
  static const Expr *funoBody(const Expr *a1, const Expr *a2,
                              unsigned bitWidth) {
    return Expr::or_(applyCompFn("$isnan", bitWidth, {a1}),
                     applyCompFn("$isnan", bitWidth, {a2}));
  }

  // generate fp predicate function body that follows the pattern p1 || p2 where
  // p1 and p2
  // are fp predicates
  static std::function<const Expr *(const Expr *, const Expr *, unsigned)>
  fpPredDisjuncBody(std::string opName) {
    return [opName](const Expr *a1, const Expr *a2, unsigned bitWidth) {
      return Expr::or_(funoBody(a1, a2, bitWidth),
                       applyCompFn(opName, bitWidth, {a1, a2}));
    };
  }

  // generate function bodies for `ftrue` and `ffalse`
  template <bool VALUE>
  static const Expr *fpLitBody(const Expr *a1, const Expr *a2,
                               unsigned bitWidth) {
    return Expr::lit(VALUE);
  }

  // generate inlined fp predicate function body
  static const Expr *fpPredExpr(std::string opName, const Expr *a1,
                                const Expr *a2, unsigned bitWidth) {
    static const std::map<
        std::string,
        std::function<const Expr *(const Expr *, const Expr *, unsigned)>>
        fpPredExprTable{{"fone", fpPredNegBody("$fueq")},
                        {"ford", fpPredNegBody("$funo")},
                        {"fueq", fpPredDisjuncBody("$foeq")},
                        {"fugt", fpPredDisjuncBody("$fogt")},
                        {"fuge", fpPredDisjuncBody("$foge")},
                        {"fult", fpPredDisjuncBody("$folt")},
                        {"fule", fpPredDisjuncBody("$fole")},
                        {"fune", fpPredDisjuncBody("$fone")},
                        {"funo", funoBody},
                        {"ffalse", fpLitBody<false>},
                        {"ftrue", fpLitBody<true>}};

    auto ret = fpPredExprTable.at(opName)(a1, a2, bitWidth);
    return ret;
  }
};

void FpOpGen::generatePreds(std::stringstream &s) const {
  describe("Floating-point predicates", s);

  const auto fpBuiltinOp = new BuiltinOp<FpOp::attrT>(FpOp::fpAttrFunc);
  const auto fpInlinedPred = new InlinedOp<FpPred::exprT>(FpPred::fpPredExpr);
  const std::vector<FpPred> fpPredTable{{"isnormal", 1, false, fpBuiltinOp},
                                        {"issubnormal", 1, false, fpBuiltinOp},
                                        {"iszero", 1, false, fpBuiltinOp},
                                        {"isinfinite", 1, false, fpBuiltinOp},
                                        {"isnan", 1, false, fpBuiltinOp},
                                        {"isnegative", 1, false, fpBuiltinOp},
                                        {"ispositive", 1, false, fpBuiltinOp},
                                        {"foeq", 2, true, fpBuiltinOp},
                                        {"fole", 2, true, fpBuiltinOp},
                                        {"folt", 2, true, fpBuiltinOp},
                                        {"foge", 2, true, fpBuiltinOp},
                                        {"fogt", 2, true, fpBuiltinOp},
                                        {"fone", 2, true, fpInlinedPred},
                                        {"ford", 2, true, fpInlinedPred},
                                        {"fueq", 2, true, fpInlinedPred},
                                        {"fugt", 2, true, fpInlinedPred},
                                        {"fuge", 2, true, fpInlinedPred},
                                        {"fult", 2, true, fpInlinedPred},
                                        {"fule", 2, true, fpInlinedPred},
                                        {"fune", 2, true, fpInlinedPred},
                                        {"funo", 2, true, fpInlinedPred},
                                        {"ffalse", 2, true, fpInlinedPred},
                                        {"ftrue", 2, true, fpInlinedPred}};

  for (auto &p : fpPredTable) {
    if (SmackOptions::FloatEnabled)
      for (auto bw : FP_BIT_WIDTHS)
        s << p.getModeledFpFunc(bw) << "\n";
    else {
      auto func = p.getUninterpretedFpFunc();
      if (func)
        s << func << "\n";
    }
  }
}

void FpOpGen::generateConvOps(std::stringstream &s) const {
  describe("Floating-point conversion", s);

  if (SmackOptions::FloatEnabled) {
    for (auto srcBw : FP_BIT_WIDTHS) {
      for (auto desBw : FP_BIT_WIDTHS) {
        if (srcBw != desBw) {
          std::string name = srcBw < desBw ? "$fpext" : "$fptrunc";

          auto exp = FP_LAYOUT.at(desBw).first;
          auto sig = FP_LAYOUT.at(desBw).second;
          std::string srcType = getFpTypeName(srcBw);
          std::string desType = getFpTypeName(desBw);
          std::string attr = "(_ to_fp " + std::to_string(exp) + " " +
                             std::to_string(sig) + ")";
          std::list<Binding> bs = makeFpVars(1, srcBw);

          bs.insert(bs.begin(), {makeRMODEVarName(), getRMODETypeName()});
          // e.g., function {:builtin "(_ to_fp 8 24)"}
          // $fpext.bvhalf.bvfloat(rm: rmode, f: bvhalf) returns (bvfloat);
          s << builtinOp(name, makeBuiltinAttr(attr), {srcType, desType}, bs,
                         desType)
            << "\n";
        }
      }
    }
  } else {
    std::string srcType = getFpTypeName(0);
    std::string desType = getFpTypeName(0);
    // e.g., function $fpext.float(f: float) returns (float);
    s << uninterpretedOp("$fpext", {srcType, desType}, makeFpVars(1, 0),
                         desType)
      << "\n";
    s << uninterpretedOp("$fptrunc", {srcType, desType}, makeFpVars(1, 0),
                         desType)
      << "\n";
  }
}

struct FpOpGen::FpIntConv {
  typedef const Attr *(*attrT)(unsigned, unsigned);
  std::string opName;
  bool f2i;
  bool bitCast;
  Op *modeledFpOp;

  FpIntConv(std::string opName, bool f2i, bool bitCast, Op *modeledFpOp)
      : opName(opName), f2i(f2i), bitCast(bitCast), modeledFpOp(modeledFpOp) {}

  FuncDecl *getUninterpretedFpIntCast(unsigned fpBw, unsigned intBw,
                                      bool rMode) const {
    std::string srcType = f2i ? getFpTypeName(fpBw) : getIntTypeName(intBw);
    std::string desType = f2i ? getIntTypeName(intBw) : getFpTypeName(fpBw);
    std::list<Binding> bs = f2i ? makeFpVars(1, fpBw) : makeIntVars(1, srcType);

    if (rMode)
      bs.insert(bs.begin(), {makeRMODEVarName(), getRMODETypeName()});

    // e.g., function $fp2ui.bvhalf.i1(rm: rmode, f: bvhalf) returns (i1);
    return uninterpretedOp("$" + opName, {srcType, desType}, bs, desType);
  }

  FuncDecl *getModeledFpFunc(unsigned fpBw, unsigned intBw) const {
    // Note that these functions are used in math.c
    // which is not sensitive to the flags.
    // So we have to include all of the conversion.

    // Warning: undefined behaviors can occur
    // https://llvm.org/docs/LangRef.html#uitofp-to-instruction
    if (!SmackOptions::BitPrecise)
      return getUninterpretedFpIntCast(fpBw, intBw, !bitCast);

    std::string srcType = f2i ? getFpTypeName(fpBw) : getBvTypeName(intBw);
    std::string desType = f2i ? getBvTypeName(intBw) : getFpTypeName(fpBw);
    std::list<Binding> bs = f2i ? makeFpVars(1, fpBw) : makeIntVars(1, srcType);
    std::string name = "$" + opName;

    if (!bitCast)
      bs.insert(bs.begin(), {makeRMODEVarName(), getRMODETypeName()});
    if (auto bop = dyn_cast<BuiltinOp<attrT>>(modeledFpOp))
      // e.g., function {:builtin "(_ fp.to_sbv 1)"}
      // $fp2si.bvhalf.bv1(rm: rmode, f: bvhalf) returns (bv1);
      return builtinOp(name, ((attrT)bop->func)(fpBw, intBw),
                       {srcType, desType}, bs, desType);
    else if (isa<UninterpretedOp>(modeledFpOp))
      // e.g., function $bitcast.bvhalf.bv16(f: bvhalf) returns (bv16);
      return uninterpretedOp(name, {srcType, desType}, bs, desType);
    else
      llvm_unreachable("no inlined fp/bv cast");
  }

  FuncDecl *getUninterpretedFpFunc(unsigned intBw) const {
    if (!SmackOptions::BitPrecise)
      return getUninterpretedFpIntCast(0, intBw, false);

    std::string srcType = f2i ? getFpTypeName(0) : getBvTypeName(intBw);
    std::string desType = f2i ? getBvTypeName(intBw) : getFpTypeName(0);
    std::list<Binding> bs = f2i ? makeFpVars(1, 0) : makeIntVars(1, srcType);

    // e.g., function $fp2ui.float.i1(f: float) returns (i1);
    return uninterpretedOp("$" + opName, {srcType, desType}, bs, desType);
  }

  // generate bv to fp bitcast builtin attribute such as `:builtin "(_ to_fp 5
  // 11)"`
  static const Attr *bitcastAttr(unsigned fpBw, unsigned intBw) {
    std::string attr = "(_ to_fp " + std::to_string(FP_LAYOUT.at(fpBw).first) +
                       " " + std::to_string(FP_LAYOUT.at(fpBw).second) + ")";
    return makeBuiltinAttr(attr);
  }

  // generate fp/bv conversion builtin attribute such as `:builtin "(_ fp.to_sbv
  // 1)"`
  template <bool SIGN, bool F2I>
  static const Attr *fpIntAttr(unsigned fpBw, unsigned intBw) {
    std::string signLetter = SIGN ? "s" : "u";
    std::string attr =
        F2I ? ("(_ fp.to_" + signLetter + "bv " + std::to_string(intBw) + ")")
            : (std::string("(_ to_fp") + (SIGN ? " " : "_unsigned ") +
               std::to_string(FP_LAYOUT.at(fpBw).first) + " " +
               std::to_string(FP_LAYOUT.at(fpBw).second) + ")");
    return makeBuiltinAttr(attr);
  }
};

void FpOpGen::generateFpIntConv(std::stringstream &s) const {
  describe("Floating-point/integer conversion", s);

  auto uninterpretedOp = new UninterpretedOp();
  const std::vector<FpIntConv> fpIntConvTable{
      {"bitcast", true, true, uninterpretedOp},
      {"bitcast", false, true,
       new BuiltinOp<FpIntConv::attrT>(FpIntConv::bitcastAttr)},
      {"fp2si", true, false,
       new BuiltinOp<FpIntConv::attrT>(FpIntConv::fpIntAttr<true, true>)},
      {"fp2ui", true, false,
       new BuiltinOp<FpIntConv::attrT>(FpIntConv::fpIntAttr<false, true>)},
      {"si2fp", false, false,
       new BuiltinOp<FpIntConv::attrT>(FpIntConv::fpIntAttr<true, false>)},
      {"ui2fp", false, false,
       new BuiltinOp<FpIntConv::attrT>(FpIntConv::fpIntAttr<false, false>)},
  };

  for (auto &conv : fpIntConvTable) {
    if (SmackOptions::FloatEnabled) {
      for (auto bw : FP_BIT_WIDTHS) {
        for (auto is : IntOpGen::INTEGER_SIZES) {
          if (!conv.bitCast || bw == is)
            s << conv.getModeledFpFunc(bw, is) << "\n";
        }
      }
    } else {
      for (auto is : IntOpGen::INTEGER_SIZES)
        if (!conv.bitCast || is == 8 ||
            std::find(FP_BIT_WIDTHS.begin(), FP_BIT_WIDTHS.end(), is) !=
                FP_BIT_WIDTHS.end())
          s << conv.getUninterpretedFpFunc(is) << "\n";
    }
  }
}

void FpOpGen::generateMemOps(std::stringstream &s) const {
  describe("Floating-point load/store operations", s);

  if (SmackOptions::FloatEnabled) {
    for (auto bw : FP_BIT_WIDTHS) {
      std::string type = getFpTypeName(bw);
      auto binding = makeFpVars(1, bw).front();
      // e.g., function {:inline} $load.bvhalf(M: [ref] bvhalf, p: ref)
      // returns (bvhalf) { M[p] }
      s << prelude.safeLoad(type) << "\n";
      // e.g., function {:inline} $store.bvhalf(M: [ref] bvhalf, p: ref, f:
      // bvhalf)
      // returns ([ref] bvhalf) { M[p := f] }
      s << prelude.safeStore(binding) << "\n";

      if (SmackOptions::BitPrecise) {
        std::string bvType = getBvTypeName(bw);
        // e.g., function {:inline} $load.bytes.bvhalf(M: [ref] bv8, p: ref)
        // returns (bvhalf) { $bitcast.bv16.bvhalf($load.bytes.bv16(M, p)) }
        s << prelude.unsafeLoad(
                 type,
                 Expr::fn(indexedName("$bitcast", {bvType, type}),
                          Expr::fn(indexedName("$load", {"bytes", bvType}),
                                   makeMapVarExpr(0), makePtrVarExpr(0))))
          << "\n";
        // e.g., function {:inline} $store.bytes.bvhalf(M: [ref] bv8, p: ref, f:
        // bvhalf)
        // returns ([ref] bv8) { $store.bytes.bv16(M, p,
        // $bitcast.bvhalf.bv16(f)) }
        s << prelude.unsafeStore(
                 binding,
                 Expr::fn(indexedName("$store", {"bytes", bvType}),
                          makeMapVarExpr(0), makePtrVarExpr(0),
                          Expr::fn(indexedName("$bitcast", {type, bvType}),
                                   makeFpVarExpr(0))))
          << "\n";
      } else {
        std::string intType = getIntTypeName(bw);
        // e.g., function {:inline} $load.unsafe.bvhalf(M: [ref] i8, p: ref)
        // returns (bvhalf) { $bitcast.i16.bvhalf($load.i16(M, p)) }
        s << prelude.unsafeLoad(
                 type,
                 Expr::fn(indexedName("$bitcast", {intType, type}),
                          Expr::fn(indexedName("$load", {intType}),
                                   makeMapVarExpr(0), makePtrVarExpr(0))),
                 false)
          << "\n";
        // e.g., function {:inline} $store.unsafe.bvfloat(M: [ref] i8, p: ref,
        // f: bvfloat)
        // returns ([ref] i8) { $store.i32(M, p, $bitcast.bvfloat.i32(f)) }
        s << prelude.unsafeStore(
                 binding,
                 Expr::fn(indexedName("$store", {intType}), makeMapVarExpr(0),
                          makePtrVarExpr(0),
                          Expr::fn(indexedName("$bitcast", {type, intType}),
                                   makeFpVarExpr(0))),
                 false)
          << "\n";
      }
    }
  } else {
    std::string type = getFpTypeName(0);
    auto binding = makeFpVars(1, 0).front();
    // function {:inline} $load.float(M: [ref] float, p: ref) returns (float) {
    // M[p] }
    s << prelude.safeLoad(type) << "\n";
    // function {:inline} $store.float(M: [ref] float, p: ref, f: float)
    // returns ([ref] float) { M[p := f] }
    s << prelude.safeStore(binding) << "\n";

    if (SmackOptions::BitPrecise) {
      std::string bvType = getBvTypeName(8);
      // function {:inline} $load.bytes.float(M: [ref] bv8, p: ref)
      // returns (float) { $bitcast.bv8.float(M[p]) }
      s << prelude.unsafeLoad(type,
                              Expr::fn(indexedName("$bitcast", {bvType, type}),
                                       prelude.mapSelExpr(0)))
        << "\n";
      // function {:inline} $store.bytes.float(M: [ref] bv8, p: ref, f: float)
      // returns ([ref] bv8) { M[p := $bitcast.float.bv8(f)] }
      s << prelude.unsafeStore(
               binding, prelude.mapUpdExpr(
                            0, Expr::fn(indexedName("$bitcast", {type, bvType}),
                                        makeFpVarExpr(0))))
        << "\n";
    } else {
      std::string intType = getIntTypeName(8);
      // function {:inline} $load.unsafe.float(M: [ref] i8, p: ref)
      // returns (float) { $bitcast.i8.float(M[p]) }
      s << prelude.unsafeLoad(type,
                              Expr::fn(indexedName("$bitcast", {intType, type}),
                                       prelude.mapSelExpr(0)),
                              false)
        << "\n";
      // function {:inline} $store.unsafe.float(M: [ref] i8, p: ref, f: float)
      // returns ([ref] i8) { M[p := $bitcast.float.i8(f)] }
      s << prelude.unsafeStore(
               binding,
               prelude.mapUpdExpr(
                   0, Expr::fn(indexedName("$bitcast", {type, intType}),
                               makeFpVarExpr(0))),
               false)
        << "\n";
    }
  }
}

void FpOpGen::generateExtractValueFuncs(std::stringstream &s) const {
  if (SmackOptions::FloatEnabled) {
    for (auto bw : FP_BIT_WIDTHS)
      s << extractValue(getFpTypeName(bw)) << "\n";
  } else
    s << extractValue(Naming::UNINTERPRETED_FLOAT_TYPE) << "\n";
}

void FpOpGen::generate(std::stringstream &s) const {
  // generate type-specific declarations
  if (SmackOptions::FloatEnabled) {
    // rounding mode declaration
    // var $rmode: rmode;
    s << Decl::variable(Naming::RMODE_VAR, getRMODETypeName());
  } else {
    // uninterpreted floating-point type constructor
    // function $fp(ipart:int, fpart:int, epart:int) returns (float);
    s << Decl::function("$fp",
                        {{"ipart", "int"}, {"fpart", "int"}, {"epart", "int"}},
                        getFpTypeName(0), nullptr, {})
      << "\n";
  }

  generateArithOps(s);
  generatePreds(s);
  generateFpIntConv(s);
  generateConvOps(s);
  generateMemOps(s);
  generateExtractValueFuncs(s);
}

std::string Prelude::getPrelude() {
  std::stringstream s;

  typeDeclGen->generate(s);
  constDeclGen->generate(s);
  memDeclGen->generate(s);
  intOpGen->generate(s);
  ptrOpGen->generate(s);
  fpOpGen->generate(s);

  return s.str();
}

} // namespace smack
