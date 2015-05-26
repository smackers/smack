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

#define LIMIT_1 2
#define LIMIT_7 128
#define LIMIT_8 256
#define LIMIT_15 32768
#define LIMIT_16 65536
#define LIMIT_31 2147483648
#define LIMIT_32 4294967296
#define LIMIT_63 9223372036854775808
#define LIMIT_64 18446744073709551616

#define xstr(s) str(s)
#define str(s) #s

#define RECORD_PROC(type) \
  procedure boogie_si_record_ ## type (i: type);

#define UNINTERPRETED_UNARY_OP(type,name) \
  function name.type(i: type) returns (type);

#define UNINTERPRETED_BINARY_OP(type,name) \
  function name.type(i1: type, i2: type) returns (type);

#define UNINTERPRETED_BINARY_PRED(type,name) \
  function name.type(i1: type, i2: type) returns (i1);

#define INLINE_UNARY_OP(type,name,body) \
  function {:inline} name.type(i: type) returns (type) body

#define INLINE_BINARY_OP(type,name,body) \
  function {:inline} name.type(i1: type, i2: type) returns (type) body

#define INLINE_BINARY_PRED(type,name,cond) \
  function {:inline} name.type.bool(i1: type, i2: type) returns (bool) {cond} \
  function {:inline} name.type(i1: type, i2: type) returns (i1) {if cond then 1 else 0}

#define INLINE_BINARY_BV_PRED(type,name,cond) \
  function {:inline} name.type.bool(i1: type, i2: type) returns (bool) {cond} \
  function {:inline} name.type(i1: type, i2: type) returns (bv1) {if cond then 1bv1 else 0bv1}

#define INLINE_CONVERSION(t1,t2,name,body) \
  function {:inline} name.t1.t2(i: t1) returns (t2) body

#define BUILTIN_UNARY_OP(type,name,prim) \
  function {:builtin xstr(prim)} name.type(i: type) returns (type);

#define BUILTIN_BINARY_OP(type,name,prim) \
  function {:builtin xstr(prim)} name.type(i1: type, i2: type) returns (type);

#define BUILTIN_BINARY_PRED(type,name,prim) \
  function {:builtin xstr(prim)} name.type(i1: type, i2: type) returns (i1);

#define BVBUILTIN_UNARY_OP(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type(i: type) returns (type);

#define BVBUILTIN_BINARY_OP(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type(i1: type, i2: type) returns (type);

#define BVBUILTIN_BINARY_PRED(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type(i1: type, i2: type) returns (i1);

#define INLINE_BVBUILTIN_BINARY_PRED(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type.bool(i1: type, i2: type) returns (bool); \
  function {:inline} name.type(i1: type, i2: type) returns (bv1) {if name.type.bool(i1,i2) then 1bv1 else 0bv1}

#define INLINE_BVBUILTIN_BINARY_SELECT(type,name,pred) \
  function {:inline} name.type(i1: type, i2: type) returns (type) {if pred.type.bool(i1,i2) then i1 else i2}

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

  DECLARE(INLINE_CONVERSION,ref,ref,$bitcast,{i});

  // BITVECTOR MODELING

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

  DECLARE_EACH_BV_TYPE(INLINE_BINARY_BV_PRED, $eq, i1 == i2)
  DECLARE_EACH_BV_TYPE(INLINE_BINARY_BV_PRED, $ne, i1 != i2)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $ule, bvule)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $ult, bvult)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $uge, bvuge)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $ugt, bvugt)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $sle, bvsle)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $slt, bvslt)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $sge, bvsge)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $sgt, bvsgt)

  DECLARE(INLINE_CONVERSION,bv64,bv32,$trunc,{i[32:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv32,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv32,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv32,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv16,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv16,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv8,bv1,$trunc,{i[1:0]});

  DECLARE(INLINE_CONVERSION,bv1,bv8,$zext,{if i == 0bv1 then 0bv8 else 1bv8});
  DECLARE(INLINE_CONVERSION,bv1,bv16,$zext,{if i == 0bv1 then 0bv16 else 1bv16});
  DECLARE(INLINE_CONVERSION,bv1,bv32,$zext,{if i == 0bv1 then 0bv32 else 1bv32});
  DECLARE(INLINE_CONVERSION,bv1,bv64,$zext,{if i == 0bv1 then 0bv64 else 1bv64});
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv8.bv16(i: bv8) returns (bv16);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv8.bv32(i: bv8) returns (bv32);");
  D("function {:bvbuiltin \"(_ zero_extend 56)\"} $zext.bv8.bv64(i: bv8) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv16.bv32(i: bv16) returns (bv32);");
  D("function {:bvbuiltin \"(_ zero_extend 48)\"} $zext.bv16.bv64(i: bv16) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv32.bv64(i: bv32) returns (bv64);");

  DECLARE(INLINE_CONVERSION,bv1,bv8,$sext,{if i == 0bv1 then 0bv8 else 255bv8});
  DECLARE(INLINE_CONVERSION,bv1,bv16,$sext,{if i == 0bv1 then 0bv16 else 65535bv16});
  DECLARE(INLINE_CONVERSION,bv1,bv32,$sext,{if i == 0bv1 then 0bv32 else 4294967295bv32});
  DECLARE(INLINE_CONVERSION,bv1,bv64,$sext,{if i == 0bv1 then 0bv64 else 18446744073709551615bv64});
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv8.bv16(i: bv8) returns (bv16);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv8.bv32(i: bv8) returns (bv32);");
  D("function {:bvbuiltin \"(_ sign_extend 56)\"} $sext.bv8.bv64(i: bv8) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv16.bv32(i: bv16) returns (bv32);");
  D("function {:bvbuiltin \"(_ sign_extend 48)\"} $sext.bv16.bv64(i: bv16) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv32.bv64(i: bv32) returns (bv64);");

  // INTEGER MODELING

  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $add, {i1 + i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $sub, {i1 - i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $mul, {i1 * i2})
  D("function {:builtin \"div\"} $div(i1: int, i2: int) returns (int);");
  D("function {:builtin \"mod\"} $mod(i1: int, i2: int) returns (int);");
  D("function {:builtin \"rem\"} $rem(i1: int, i2: int) returns (int);");
  D("function {:inline} $min(i1: int, i2: int) returns (int) {if i1 < i2 then i1 else i2}");
  D("function {:inline} $max(i1: int, i2: int) returns (int) {if i1 > i2 then i1 else i2}");

  DECLARE_EACH_INT_TYPE(BUILTIN_BINARY_OP, $sdiv, div)
  DECLARE_EACH_INT_TYPE(BUILTIN_BINARY_OP, $smod, mod)
  DECLARE_EACH_INT_TYPE(BUILTIN_BINARY_OP, $srem, rem)
  DECLARE_EACH_INT_TYPE(BUILTIN_BINARY_OP, $udiv, div);
  DECLARE_EACH_INT_TYPE(BUILTIN_BINARY_OP, $urem, rem);

  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $smin, {$min(i1,i2)})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $smax, {$max(i1,i2)})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $umin, {$min(i1,i2)})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_OP, $umax, {$max(i1,i2)})

  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $shl)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $lshr)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $ashr)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_UNARY_OP, $not)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $and)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $or)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $xor)
  DECLARE_EACH_INT_TYPE(UNINTERPRETED_BINARY_OP, $nand)

  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $eq, i1 == i2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ne, i1 != i2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ule, i1 <= i2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ult, i1 < i2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $uge, i1 >= i2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ugt, i1 > i2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $sle, i1 <= i2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $slt, i1 < i2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $sge, i1 >= i2)
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $sgt, i1 > i2)

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

  DECLARE(INLINE_CONVERSION,i64,i32,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i64,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i64,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i64,i1,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i32,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i32,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i32,i1,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i16,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i16,i1,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i8,i1,$trunc,{i});

  DECLARE(INLINE_CONVERSION,i1,i8,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i16,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i32,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i16,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i32,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i32,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i64,$zext,{i});

  DECLARE(INLINE_CONVERSION,i1,i8,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i16,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i16,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i64,$sext,{i});

  D("type float;");
  D("function $fp(ipart:int, fpart:int, epart:int) returns (float);");
  D("function $fadd.float(f1:float, f2:float) returns (float);");
  D("function $fsub.float(f1:float, f2:float) returns (float);");
  D("function $fmul.float(f1:float, f2:float) returns (float);");
  D("function $fdiv.float(f1:float, f2:float) returns (float);");
  D("function $frem.float(f1:float, f2:float) returns (float);");
  D("function $ffalse.float(f1:float, f2:float) returns (i1);");
  D("function $ftrue.float(f1:float, f2:float) returns (i1);");
  D("function {:inline} $foeq.float(f1:float, f2:float) returns (i1) { if $foeq.bool(f1,f2) then 1 else 0 }");
  D("function $foeq.bool(f1:float, f2:float) returns (bool);");
  D("function $foge.float(f1:float, f2:float) returns (i1);");
  D("function $fogt.float(f1:float, f2:float) returns (i1);");
  D("function $fole.float(f1:float, f2:float) returns (i1);");
  D("function $folt.float(f1:float, f2:float) returns (i1);");
  D("function $fone.float(f1:float, f2:float) returns (i1);");
  D("function $ford.float(f1:float, f2:float) returns (i1);");
  D("function $fueq.float(f1:float, f2:float) returns (i1);");
  D("function $fuge.float(f1:float, f2:float) returns (i1);");
  D("function $fugt.float(f1:float, f2:float) returns (i1);");
  D("function $fule.float(f1:float, f2:float) returns (i1);");
  D("function $fult.float(f1:float, f2:float) returns (i1);");
  D("function $fune.float(f1:float, f2:float) returns (i1);");
  D("function $funo.float(f1:float, f2:float) returns (i1);");
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

  D("procedure $alloc(n: ref) returns (p: ref)\n"
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

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
  D("var $Alloc: [ref] bool;");
  D("var $Size: [ref] ref;");
  D("var $CurrAddr:ref;");

  D("procedure $alloc(n: ref) returns (p: ref);\n"
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

#else // NO_REUSE does not reuse previously-allocated addresses
  D("var $Alloc: [ref] bool;");
  D("var $CurrAddr:ref;");
  D("procedure $alloc(n: ref) returns (p: ref);\n"
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
#endif

  D("var $exn: bool;");
  D("var $exnv: int;");
  D("function $extractvalue(p: int, i: int) returns (int);");

#undef D
}

