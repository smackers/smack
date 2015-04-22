//
// This file is distributed under the MIT License. See LICENSE for details.

#include "smack.h"

/**
 * The SMACK "prelude" definitions
 *
 * TODO add more documentation
 *
 * NOTES ON MEMORY MODELS
 *
 * 1. addresses are (unbounded) integers
 * 2. one unbounded integer is stored at each address
 * 3. (NO-REUSE only) heap addresses are allocated in a strictly increasing
 *    fashion
 * 4. (NO-REUSE only) freed (heap) addresses are never reallocated
 * 5. the address space is partitioned as follows
 *
 * Address A                                        Allocation
 * ---------                                        ----------
 * A > 0                                            Heap
 * A = 0                                            Not allocated (null)
 * $GLOBALS_BOTTOM <= A < 0                         Static (global storage)
 * $GLOBALS_BOTTOM - 32768 < A < $GLOBALS_BOTTOM    Not allocated (padding)
 * A < $GLOBALS_BOTTOM - 32768                      External
 *
 */

void __SMACK_dummy(int v) {
  __SMACK_code("assume true;");
}

#define xstr(s) str(s)
#define str(s) #s

#define RECORD_PROC(type) \
  procedure boogie_si_record_ ## type (i: type);

#define UNINTERPRETED_UNARY_OP(type,name) \
  function name.type(p: type) returns (type);

#define UNINTERPRETED_BINARY_OP(type,name) \
  function name.type(p1: type, p2: type) returns (type);

#define UNINTERPRETED_BINARY_PRED(type,name) \
  function name.type(p1: type, p2: type) returns (i1);

#define INLINE_UNARY_OP(type,name,body) \
  function {:inline} name.type(p: type) returns (type) body

#define INLINE_BINARY_OP(type,name,body) \
  function {:inline} name.type(p1: type, p2: type) returns (type) body

#define INLINE_BINARY_PRED(type,name,cond) \
  function {:inline} name.type.bool(p1: type, p2: type) returns (bool) {cond} \
  function {:inline} name.type(p1: type, p2: type) returns (i1) {if cond then 1 else 0}

#define INLINE_BINARY_BV_PRED(type,name,body) \
  function {:inline} name.type(p1: type, p2: type) returns (bv1) body

#define INLINE_CONVERSION(t1,t2,name,body) \
  function {:inline} name.t1.t2(p: t1) returns (t2) body

#define BUILTIN_UNARY_OP(type,name,prim) \
  function {:builtin xstr(prim)} name.type(p: type) returns (type);

#define BUILTIN_BINARY_OP(type,name,prim) \
  function {:builtin xstr(prim)} name.type(p1: type, p2: type) returns (type);

#define BUILTIN_BINARY_PRED(type,name,prim) \
  function {:builtin xstr(prim)} name.type(p1: type, p2: type) returns (i1);

#define BVBUILTIN_UNARY_OP(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type(p: type) returns (type);

#define BVBUILTIN_BINARY_OP(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type(p1: type, p2: type) returns (type);

#define BVBUILTIN_BINARY_PRED(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type(p1: type, p2: type) returns (i1);

#define INLINE_BVBUILTIN_BINARY_PRED(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type.bool(p1: type, p2: type) returns (bool); \
  function {:inline} name.type(p1: type, p2: type) returns (bv1) {if name.type.bool(p1,p2) then 1bv1 else 0bv1}

#define INLINE_BVBUILTIN_BINARY_SELECT(type,name,pred) \
  function {:inline} name.type(p1: type, p2: type) returns (type) {if pred.type.bool(p1,p2) then p1 else p2}

#define D(d) __SMACK_top_decl(d)

#define DECLARE(M,args...) \
  D(xstr(M(args)))

#define DECLARE_EACH_INT_TYPE(M,args...) \
  D(xstr(M(i64,args))); \
  D(xstr(M(i32,args))); \
  D(xstr(M(i16,args))); \
  D(xstr(M(i8,args))); \
  D(xstr(M(i1,args)));

#define DECLARE_EACH_BV_TYPE(M,args...) \
  D(xstr(M(bv64,args))); \
  D(xstr(M(bv32,args))); \
  D(xstr(M(bv16,args))); \
  D(xstr(M(bv8,args))); \
  D(xstr(M(bv1,args)));

void __SMACK_decls() {

  D("type i1 = int;");
  D("type i8 = int;");
  D("type i16 = int;");
  D("type i32 = int;");
  D("type i64 = int;");

  D("const $0.ref, $1.ref, $2.ref, $3.ref, $4.ref, $5.ref, $6.ref, $7.ref: ref;");

  DECLARE_EACH_BV_TYPE(BVBUILTIN_UNARY_OP, $neg, bvneg)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $add, bvadd)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $sub, bvsub)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $mul, bvmul)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $udiv, bvudiv)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $sdiv, bvsdiv)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $smod, bvsmod)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $srem, bvsrem)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $urem, bvurem)

  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_SELECT, $min, $slt)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_SELECT, $max, $sgt)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_SELECT, $umin, $ult)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_SELECT, $umax, $ugt)

  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $shl, bvshl)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $lshr, bvlshr)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $ashr, bvashr)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_UNARY_OP, $not, bvnot)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $and, bvand)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $or, bvor)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $xor, bvxor)
  DECLARE_EACH_BV_TYPE(BVBUILTIN_BINARY_OP, $nand, bvnand)

  DECLARE_EACH_BV_TYPE(INLINE_BINARY_BV_PRED, $eq, {if p1 == p2 then 1bv1 else 0bv1})
  DECLARE_EACH_BV_TYPE(INLINE_BINARY_BV_PRED, $ne, {if p1 != p2 then 1bv1 else 0bv1})
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $ule, bvule)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $ult, bvult)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $uge, bvuge)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $ugt, bvugt)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $sle, bvsle)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $slt, bvslt)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $sge, bvsge)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $sgt, bvsgt)

  DECLARE(INLINE_CONVERSION,bv64,bv32,$trunc,{p[32:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv16,$trunc,{p[16:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv8,$trunc,{p[8:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv1,$trunc,{if p == 0bv64 then 0bv1 else 1bv1});
  DECLARE(INLINE_CONVERSION,bv32,bv16,$trunc,{p[16:0]});
  DECLARE(INLINE_CONVERSION,bv32,bv8,$trunc,{p[8:0]});
  DECLARE(INLINE_CONVERSION,bv32,bv1,$trunc,{if p == 0bv32 then 0bv1 else 1bv1});
  DECLARE(INLINE_CONVERSION,bv16,bv8,$trunc,{p[8:0]});
  DECLARE(INLINE_CONVERSION,bv16,bv1,$trunc,{if p == 0bv16 then 0bv1 else 1bv1});
  DECLARE(INLINE_CONVERSION,bv8,bv1,$trunc,{if p == 0bv8 then 0bv1 else 1bv1});

  DECLARE(INLINE_CONVERSION,bv1,bv8,$zext,{if p == 0bv1 then 0bv8 else 1bv8});
  DECLARE(INLINE_CONVERSION,bv1,bv16,$zext,{if p == 0bv1 then 0bv16 else 1bv16});
  DECLARE(INLINE_CONVERSION,bv1,bv32,$zext,{if p == 0bv1 then 0bv32 else 1bv32});
  DECLARE(INLINE_CONVERSION,bv1,bv64,$zext,{if p == 0bv1 then 0bv64 else 1bv64});
  DECLARE(INLINE_CONVERSION,bv8,bv16,$zext,{0bv8 ++ p});
  DECLARE(INLINE_CONVERSION,bv8,bv32,$zext,{0bv24 ++ p});
  DECLARE(INLINE_CONVERSION,bv8,bv64,$zext,{0bv56 ++ p});
  DECLARE(INLINE_CONVERSION,bv16,bv32,$zext,{0bv16 ++ p});
  DECLARE(INLINE_CONVERSION,bv16,bv64,$zext,{0bv48 ++ p});
  DECLARE(INLINE_CONVERSION,bv32,bv64,$zext,{0bv32 ++ p});

  DECLARE(INLINE_CONVERSION,bv1,bv8,$sext,{if p == 0bv1 then 0bv8 else 1bv8});
  DECLARE(INLINE_CONVERSION,bv1,bv16,$sext,{if p == 0bv1 then 0bv16 else 1bv16});
  DECLARE(INLINE_CONVERSION,bv1,bv32,$sext,{if p == 0bv1 then 0bv32 else 1bv32});
  DECLARE(INLINE_CONVERSION,bv1,bv64,$sext,{if p == 0bv1 then 0bv64 else 1bv64});
  DECLARE(INLINE_CONVERSION,bv8,bv16,$sext,{if $sge.bv8.bool(p, 0bv8) then $zext.bv8.bv16(p) else $neg.bv8(1bv8) ++ p});
  DECLARE(INLINE_CONVERSION,bv8,bv32,$sext,{if $sge.bv8.bool(p, 0bv8) then $zext.bv8.bv32(p) else $neg.bv32(1bv32)[32:8] ++ p});
  DECLARE(INLINE_CONVERSION,bv8,bv64,$sext,{if $sge.bv8.bool(p, 0bv8) then $zext.bv8.bv64(p) else $neg.bv64(1bv64)[64:8] ++ p});
  DECLARE(INLINE_CONVERSION,bv16,bv32,$sext,{if $sge.bv16.bool(p, 0bv16) then $zext.bv16.bv32(p) else $neg.bv16(1bv16) ++ p});
  DECLARE(INLINE_CONVERSION,bv16,bv64,$sext,{if $sge.bv16.bool(p, 0bv16) then $zext.bv16.bv64(p) else $neg.bv64(1bv64)[64:16] ++ p});
  DECLARE(INLINE_CONVERSION,bv32,bv64,$sext,{if $sge.bv32.bool(p, 0bv32) then $zext.bv32.bv64(p) else $neg.bv32(1bv32) ++ p});

  DECLARE_EACH_INT_TYPE(INLINE_UNARY_OP, $neg, {0 - p})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $add, {p1 + p2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $sub, {p1 - p2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $mul, {p1 * p2})
  DECLARE_EACH_INT_TYPE(BUILTIN_BINARY_OP, $udiv, div)
  DECLARE_EACH_INT_TYPE(BUILTIN_BINARY_OP, $sdiv, div)
  DECLARE_EACH_INT_TYPE(BUILTIN_BINARY_OP, $smod, mod)
  DECLARE_EACH_INT_TYPE(BUILTIN_BINARY_OP, $srem, rem)
  DECLARE_EACH_INT_TYPE(BUILTIN_BINARY_OP, $urem, rem)

  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $min, {if p1 < p2 then p1 else p2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $max, {if p1 > p2 then p1 else p2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $umin, {if p1 < p2 then p1 else p2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $umax, {if p1 > p2 then p1 else p2})

  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $shl)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $lshr)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $ashr)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_UNARY_OP, $not)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $and)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $or)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $xor)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $nand)

  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $eq, p1 == p2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ne, p1 != p2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ule, p1 <= p2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ult, p1 < p2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $uge, p1 >= p2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ugt, p1 > p2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $sle, p1 <= p2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $slt, p1 < p2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $sge, p1 >= p2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $sgt, p1 > p2)

  D("axiom $and.i1(0,0) == 0;");
  D("axiom $and.i1(0,1) == 0;");
  D("axiom $and.i1(1,0) == 0;");
  D("axiom $and.i1(1,1) == 1;");
  D("axiom $or.i1(0,0) == 0;");
  D("axiom $or.i1(0,1) == 1;");
  D("axiom $or.i1(1,0) == 1;");
  D("axiom $or.i1(1,1) == 1;");
  D("axiom $xor.i1(0,0) == 0;");
  D("axiom $xor.i1(0,1) == 1;");
  D("axiom $xor.i1(1,0) == 1;");
  D("axiom $xor.i1(1,1) == 0;");

  DECLARE(INLINE_CONVERSION,i64,i32,$trunc,{p});
  DECLARE(INLINE_CONVERSION,i64,i16,$trunc,{p});
  DECLARE(INLINE_CONVERSION,i64,i8,$trunc,{p});
  DECLARE(INLINE_CONVERSION,i64,i1,$trunc,{p});
  DECLARE(INLINE_CONVERSION,i32,i16,$trunc,{p});
  DECLARE(INLINE_CONVERSION,i32,i8,$trunc,{p});
  DECLARE(INLINE_CONVERSION,i32,i1,$trunc,{p});
  DECLARE(INLINE_CONVERSION,i16,i8,$trunc,{p});
  DECLARE(INLINE_CONVERSION,i16,i1,$trunc,{p});
  DECLARE(INLINE_CONVERSION,i8,i1,$trunc,{p});

  DECLARE(INLINE_CONVERSION,i1,i8,$zext,{p});
  DECLARE(INLINE_CONVERSION,i1,i16,$zext,{p});
  DECLARE(INLINE_CONVERSION,i1,i32,$zext,{p});
  DECLARE(INLINE_CONVERSION,i1,i64,$zext,{p});
  DECLARE(INLINE_CONVERSION,i8,i16,$zext,{p});
  DECLARE(INLINE_CONVERSION,i8,i32,$zext,{p});
  DECLARE(INLINE_CONVERSION,i8,i64,$zext,{p});
  DECLARE(INLINE_CONVERSION,i16,i32,$zext,{p});
  DECLARE(INLINE_CONVERSION,i16,i64,$zext,{p});
  DECLARE(INLINE_CONVERSION,i32,i64,$zext,{p});

  DECLARE(INLINE_CONVERSION,i1,i8,$sext,{p});
  DECLARE(INLINE_CONVERSION,i1,i16,$sext,{p});
  DECLARE(INLINE_CONVERSION,i1,i32,$sext,{p});
  DECLARE(INLINE_CONVERSION,i1,i64,$sext,{p});
  DECLARE(INLINE_CONVERSION,i8,i16,$sext,{p});
  DECLARE(INLINE_CONVERSION,i8,i32,$sext,{p});
  DECLARE(INLINE_CONVERSION,i8,i64,$sext,{p});
  DECLARE(INLINE_CONVERSION,i16,i32,$sext,{p});
  DECLARE(INLINE_CONVERSION,i16,i64,$sext,{p});
  DECLARE(INLINE_CONVERSION,i32,i64,$sext,{p});

  D("type float;");
  D("function $fp(ipart:int, fpart:int, epart:int) returns (float);");
  D("function $fadd(f1:float, f2:float) returns (float);");
  D("function $fsub(f1:float, f2:float) returns (float);");
  D("function $fmul(f1:float, f2:float) returns (float);");
  D("function $fdiv(f1:float, f2:float) returns (float);");
  D("function $frem(f1:float, f2:float) returns (float);");
  D("function $ffalse(f1:float, f2:float) returns (i1);");
  D("function $ftrue(f1:float, f2:float) returns (i1);");
  D("function $foeq(f1:float, f2:float) returns (i1);");
  D("function $foeq.bool(f1:float, f2:float) returns (bool);");
  D("function $foge(f1:float, f2:float) returns (i1);");
  D("function $fogt(f1:float, f2:float) returns (i1);");
  D("function $fole(f1:float, f2:float) returns (i1);");
  D("function $folt(f1:float, f2:float) returns (i1);");
  D("function $fone(f1:float, f2:float) returns (i1);");
  D("function $ford(f1:float, f2:float) returns (i1);");
  D("function $fueq(f1:float, f2:float) returns (i1);");
  D("function $fuge(f1:float, f2:float) returns (i1);");
  D("function $fugt(f1:float, f2:float) returns (i1);");
  D("function $fule(f1:float, f2:float) returns (i1);");
  D("function $fult(f1:float, f2:float) returns (i1);");
  D("function $fune(f1:float, f2:float) returns (i1);");
  D("function $funo(f1:float, f2:float) returns (i1);");
  D("function $fp2si.i64(f:float) returns (i64);");
  D("function $fp2ui.i64(f:float) returns (i64);");
  D("function $si2fp.i64(i:i64) returns (float);");
  D("function $ui2fp.i64(i:i64) returns (float);");
  D("function $fp2si.i32(f:float) returns (i32);");
  D("function $fp2ui.i32(f:float) returns (i32);");
  D("function $si2fp.i32(i:i32) returns (float);");
  D("function $ui2fp.i32(i:i32) returns (float);");
  D("function $fp2si.i16(f:float) returns (i16);");
  D("function $fp2ui.i16(f:float) returns (i16);");
  D("function $si2fp.i16(i:i16) returns (float);");
  D("function $ui2fp.i16(i:i16) returns (float);");
  D("function $fp2si.i8(f:float) returns (i8);");
  D("function $fp2ui.i8(f:float) returns (i8);");
  D("function $si2fp.i8(i:i8) returns (float);");
  D("function $ui2fp.i8(i:i8) returns (float);");

  D("axiom (forall f1, f2: float :: f1 != f2 || $foeq.bool(f1,f2));");
  D("axiom (forall i: i64 :: $fp2ui.i64($ui2fp.i64(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i64($fp2ui.i64(f)) == f);");
  D("axiom (forall i: i64 :: $fp2si.i64($si2fp.i64(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i64($fp2si.i64(f)) == f);");
  D("axiom (forall i: i32 :: $fp2ui.i32($ui2fp.i32(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i32($fp2ui.i32(f)) == f);");
  D("axiom (forall i: i32 :: $fp2si.i32($si2fp.i32(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i32($fp2si.i32(f)) == f);");
  D("axiom (forall i: i16 :: $fp2ui.i16($ui2fp.i16(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i16($fp2ui.i16(f)) == f);");
  D("axiom (forall i: i16 :: $fp2si.i16($si2fp.i16(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i16($fp2si.i16(f)) == f);");
  D("axiom (forall i: i8 :: $fp2ui.i8($ui2fp.i8(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i8($fp2ui.i8(f)) == f);");
  D("axiom (forall i: i8 :: $fp2si.i8($si2fp.i8(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i8($fp2si.i8(f)) == f);");

  // Memory Model
  D("const $GLOBALS_BOTTOM: ref;");
  D("const $EXTERNS_BOTTOM: ref;");
  D("const $MALLOC_TOP: ref;");
  D("function $base(ref) returns (ref);");
  D("function {:inline} $isExternal(p: ref) returns (bool) {$slt.ref.bool(p,$EXTERNS_BOTTOM)}");

// #ifdef BITPRECISE

  D("function {:inline} $load.bv64(M:[ref]bv8, p:ref) returns (bv64){$load.bv32(M, $add.ref(p, $4.ref))++$load.bv32(M, p)}");
  D("function {:inline} $load.bv32(M:[ref]bv8, p:ref) returns (bv32){M[$add.ref(p, $3.ref)]++M[$add.ref(p, $2.ref)]++M[$add.ref(p, $1.ref)]++M[p]}");
  D("function {:inline} $load.bv16(M:[ref]bv8, p:ref) returns (bv16){M[$add.ref(p, $1.ref)]++M[p]}");
  D("function {:inline} $load.bv8(M:[ref]bv8, p:ref) returns (bv8){M[p]}");

  D("function {:inline} $store.bv64(M:[ref]bv8, p:ref, v:bv64) returns ([ref]bv8)"
    "{M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]][$add.ref(p, $2.ref) := v[24:16]][$add.ref(p, $3.ref) := v[32:24]]"
    "[$add.ref(p, $4.ref) := v[40:32]][$add.ref(p, $5.ref) := v[48:40]][$add.ref(p, $6.ref) := v[56:48]][$add.ref(p, $7.ref) := v[64:56]]}");
  D("function {:inline} $store.bv32(M:[ref]bv8, p:ref, v:bv32) returns ([ref]bv8) {M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]][$add.ref(p, $2.ref) := v[24:16]][$add.ref(p, $3.ref) := v[32:24]]}");
  D("function {:inline} $store.bv16(M:[ref]bv8, p:ref, v:bv16) returns ([ref]bv8) {M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]}");
  D("function {:inline} $store.bv8(M:[ref]bv8, p:ref, v:bv8) returns ([ref]bv8) {M[p := v]}");

// #endif

  // Memory debugging symbols
  D("type $mop;");
  D("procedure boogie_si_record_mop(m: $mop);");
  D("const $MOP: $mop;");

  DECLARE(RECORD_PROC, bool);
  DECLARE(RECORD_PROC, i1);
  DECLARE(RECORD_PROC, i8);
  DECLARE(RECORD_PROC, i16);
  DECLARE(RECORD_PROC, i32);
  DECLARE(RECORD_PROC, i64);
  DECLARE(RECORD_PROC, bv1);
  DECLARE(RECORD_PROC, bv8);
  DECLARE(RECORD_PROC, bv16);
  DECLARE(RECORD_PROC, bv32);
  DECLARE(RECORD_PROC, bv64);
  DECLARE(RECORD_PROC, ref);
  DECLARE(RECORD_PROC, float);

#if MEMORY_MODEL_NO_REUSE_IMPLS
  D("var $Alloc: [ref] bool;");
  D("var $CurrAddr:ref;");

  D("procedure $malloc(n: size) returns (p: ref)\n"
    "modifies $CurrAddr, $Alloc;\n"
    "{\n"
    "  assume $sgt.ref.bool($CurrAddr, $0.ref);\n"
    "  p := $CurrAddr;\n"
    "  if ($sgt.ref.bool(n, $0.ref)) {\n"
    "    $CurrAddr := $add.ref($CurrAddr, n);\n"
    "  } else {\n"
    "    $CurrAddr := $add.ref($CurrAddr, $1.ref);\n"
    "  }\n"
    "  $Alloc[p] := true;\n"
    "}");

  D("procedure $free(p: ref)\n"
    "modifies $Alloc;\n"
    "{\n"
    "  $Alloc[p] := false;\n"
    "}");

  D("procedure $alloca(n: size) returns (p: ref)\n"
    "modifies $CurrAddr, $Alloc;\n"
    "{\n"
    "  assume $sgt.ref.bool($CurrAddr, $0.ref);\n"
    "  p := $CurrAddr;\n"
    "  if ($sgt.ref.bool(n, $0.ref)) {\n"
    "    $CurrAddr := $add.ref($CurrAddr, n);\n"
    "  } else {\n"
    "    $CurrAddr := $add.ref($CurrAddr, $1.ref);\n"
    "  }\n"
    "  $Alloc[p] := true;\n"
    "}");

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
  D("var $Alloc: [ref] bool;");
  D("var $Size: [ref] size;");
  D("var $CurrAddr:ref;");

  D("procedure $malloc(n: size) returns (p: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $sgt.ref.bool(p, $0.ref);\n"
    "ensures $slt.ref.bool(p, $MALLOC_TOP);\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: ref :: old($Alloc[q]) ==> ($slt.ref.bool($add.ref(p, n), q) || $sgt.ref.bool(p, $add.ref(q, $Size[q]))));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $sge.ref.bool(n, $0.ref) ==> (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc;\n"
    "ensures !$Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));");

  D("procedure $alloca(n: size) returns (p: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $sgt.ref.bool(p, $0.ref);\n"
    "ensures $slt.ref.bool(p, $MALLOC_TOP);\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: ref :: old($Alloc[q]) ==> ($slt.ref.bool($add.ref(p, n), q) || $sgt.ref.bool(p, $add.ref(q, $Size[q]))));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $sge.ref.bool(n, $0.ref) ==> (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);");

#else // NO_REUSE does not reuse previously-allocated addresses
  D("var $Alloc: [ref] bool;");
  D("var $CurrAddr:ref;");
  D("procedure $malloc(n: size) returns (p: ref);\n"
    "modifies $CurrAddr, $Alloc;\n"
    "ensures $sgt.ref.bool(p, $0.ref);\n"
    "ensures p == old($CurrAddr);\n"
    "ensures $sgt.ref.bool($CurrAddr, old($CurrAddr));\n"
    "ensures $sge.ref.bool(n, $0.ref) ==> $sge.ref.bool($CurrAddr, $add.ref(old($CurrAddr), n));\n"
    "ensures $Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $sge.ref.bool(n, $0.ref) ==> (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc;\n"
    "ensures !$Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));");

  D("procedure $alloca(n: size) returns (p: ref);\n"
    "modifies $CurrAddr, $Alloc;\n"
    "ensures $sgt.ref.bool(p, $0.ref);\n"
    "ensures p == old($CurrAddr);\n"
    "ensures $sgt.ref.bool($CurrAddr, old($CurrAddr));\n"
    "ensures $sge.ref.bool(n, $0.ref) ==> $sge.ref.bool($CurrAddr, $add.ref(old($CurrAddr), n));\n"
    "ensures $Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $sge.ref.bool(n, $0.ref) ==> (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);");
#endif

  D("var $exn: bool;");
  D("var $exnv: int;");
  D("function $extractvalue(p: int, i: int) returns (int);");

#undef D
}

