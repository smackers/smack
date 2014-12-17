//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_H_
#define SMACK_H_

/**
 * The SMACK "prelude" declarations
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

#ifdef __cplusplus
extern "C" {
#endif
void __SMACK_code(const char *fmt, ...);
void __SMACK_mod(const char *fmt, ...);
void __SMACK_decl(const char *fmt, ...);
void __SMACK_top_decl(const char *fmt, ...);

// We need this to enforce that assert/assume are function calls
// with an integer argument (DSA gets confused otherwise)
__attribute__((always_inline))
void __SMACK_dummy(int v) {
  __SMACK_code("assume true;");
#endif
#ifdef BITVECTOR
	__SMACK_code("assume @ != 0bv32;", v);
#else
#endif
}

#define assert(EX) __SMACK_dummy(EX); __SMACK_code("assert @ != 0;", EX)
#define assume(EX) __SMACK_dummy(EX); __SMACK_code("assume @ != 0;", EX)

int __SMACK_nondet() {
	static int XXX;
	int x = XXX;
	__SMACK_code("havoc @;", x);
	return x;
}

void __SMACK_decls() {
#define D(d) __SMACK_top_decl(d)

	// Integer arithmetic
	#ifdef BITVECTOR
	// Bitvector arithmetic
	D("function {:bvbuiltin \"bvadd\"}   $add.i32(p1:i32, p2:i32)   returns (i32);");
	D("function {:bvbuiltin \"bvsub\"}   $sub.i32(p1:i32, p2:i32)   returns (i32);");
	D("function {:bvbuiltin \"bvmul\"}   $mul.i32(p1:i32, p2:i32)   returns (i32);");
	D("function {:bvbuiltin \"bvneg\"}   $neg.i32(p1:i32)   	    returns (i32);");
	D("function {:bvbuiltin \"bvsmod\"}  $smod.i32(p1:i32, p2:i32)   returns (i32);");
	D("function {:bvbuiltin \"bvsrem\"}  $srem.i32(p1:i32, p2:i32)   returns (i32);");
	D("function {:bvbuiltin \"bvurem\"}  $urem.i32(p1:i32, p2:i32)   returns (i32);");
	D("function {:bvbuiltin \"bvshl\"}   $shl.i32(p1:i32, p2:i32)   returns (i32);");
	D("function {:bvbuiltin \"bvlshr\"}  $lshr.i32(p1:i32, p2:i32)  returns (i32);");
	D("function {:bvbuiltin \"bvashr\"}  $ashr.i32(p1:i32, p2:i32)  returns (i32);");

	D("function {:bvbuiltin \"bvadd\"}   $add.i16(p1:i16, p2:i16)   returns (i16);");
	D("function {:bvbuiltin \"bvsub\"}   $sub.i16(p1:i16, p2:i16)   returns (i16);");
	D("function {:bvbuiltin \"bvmul\"}   $mul.i16(p1:i16, p2:i16)   returns (i16);");
	D("function {:bvbuiltin \"bvneg\"}   $neg.i16(p1:i16)   	    returns (i16);");
	D("function {:bvbuiltin \"bvsmod\"}  $smod.i16(p1:i16, p2:i16)   returns (i16);");
	D("function {:bvbuiltin \"bvsrem\"}  $srem.i16(p1:i16, p2:i16)   returns (i16);");
	D("function {:bvbuiltin \"bvurem\"}  $urem.i16(p1:i16, p2:i16)   returns (i16);");
	D("function {:bvbuiltin \"bvshl\"}   $shl.i16(p1:i16, p2:i16)   returns (i16);");
	D("function {:bvbuiltin \"bvlshr\"}  $lshr.i16(p1:i16, p2:i16)  returns (i16);");
	D("function {:bvbuiltin \"bvashr\"}  $ashr.i16(p1:i16, p2:i16)  returns (i16);");

	D("function {:bvbuiltin \"bvadd\"}   $add.i8(p1:i8, p2:i8)   returns (i8);");
	D("function {:bvbuiltin \"bvsub\"}   $sub.i8(p1:i8, p2:i8)   returns (i8);");
	D("function {:bvbuiltin \"bvmul\"}   $mul.i8(p1:i8, p2:i8)   returns (i8);");
	D("function {:bvbuiltin \"bvneg\"}   $neg.i8(p1:i8)   	    returns (i8);");
	D("function {:bvbuiltin \"bvsmod\"}  $smod.i8(p1:i8, p2:i8)   returns (i8);");
	D("function {:bvbuiltin \"bvsrem\"}  $srem.i8(p1:i8, p2:i8)   returns (i8);");
	D("function {:bvbuiltin \"bvurem\"}  $urem.i8(p1:i8, p2:i8)   returns (i8);");
	D("function {:bvbuiltin \"bvshl\"}   $shl.i8(p1:i8, p2:i8)   returns (i8);");
	D("function {:bvbuiltin \"bvlshr\"}  $lshr.i8(p1:i8, p2:i8)  returns (i8);");
	D("function {:bvbuiltin \"bvashr\"}  $ashr.i8(p1:i8, p2:i8)  returns (i8);");
	// Bitwise operations
	// Shaobo: Z3 supports more bitwise operations than listed. However, C only supports the listed ones.
	D("function {:bvbuiltin \"bvand\"}   $and.i32(p1:i32, p2:i32)   returns (i32);");
	D("function {:bvbuiltin \"bvor\"}    $or.i32(p1:i32, p2:i32)    returns (i32);");
	D("function {:bvbuiltin \"bvnot\"}   $not.i32(p1:i32)           returns (i32);");
	D("function {:bvbuiltin \"bvxor\"}   $xor.i32(p1:i32, p2:i32)   returns (i32);");

	D("function {:bvbuiltin \"bvand\"}   $and.i16(p1:i16, p2:i16)   returns (i16);");
	D("function {:bvbuiltin \"bvor\"}    $or.i16(p1:i16, p2:i16)    returns (i16);");
	D("function {:bvbuiltin \"bvnot\"}   $not.i16(p1:i16)           returns (i16);");
	D("function {:bvbuiltin \"bvxor\"}   $xor.i16(p1:i16, p2:i16)   returns (i16);");

	D("function {:bvbuiltin \"bvand\"}   $and.i8(p1:i8, p2:i8)   returns (i8);");
	D("function {:bvbuiltin \"bvor\"}    $or.i8(p1:i8, p2:i8)    returns (i8);");
	D("function {:bvbuiltin \"bvnot\"}   $not.i8(p1:i8)           returns (i8);");
	D("function {:bvbuiltin \"bvxor\"}   $xor.i8(p1:i8, p2:i8)   returns (i8);");
	// Predicates
	D("function {:bvbuiltin \"bvule\"}   $ule.i32(p1:i32, p2:i32)   returns (bool);");
	D("function {:bvbuiltin \"bvult\"}   $ult.i32(p1:i32, p2:i32)   returns (bool);");
	D("function {:bvbuiltin \"bvuge\"}   $uge.i32(p1:i32, p2:i32)   returns (bool);");
	D("function {:bvbuiltin \"bvugt\"}   $ugt.i32(p1:i32, p2:i32)   returns (bool);");
	D("function {:bvbuiltin \"bvsle\"}   $sle.i32(p1:i32, p2:i32)   returns (bool);");
	D("function {:bvbuiltin \"bvslt\"}   $slt.i32(p1:i32, p2:i32)   returns (bool);");
	D("function {:bvbuiltin \"bvsge\"}   $sge.i32(p1:i32, p2:i32)   returns (bool);");
	D("function {:bvbuiltin \"bvsgt\"}   $sgt.i32(p1:i32, p2:i32)   returns (bool);");

	D("function {:bvbuiltin \"bvule\"}   $ule.i16(p1:i16, p2:i16)   returns (bool);");
	D("function {:bvbuiltin \"bvult\"}   $ult.i16(p1:i16, p2:i16)   returns (bool);");
	D("function {:bvbuiltin \"bvuge\"}   $uge.i16(p1:i16, p2:i16)   returns (bool);");
	D("function {:bvbuiltin \"bvugt\"}   $ugt.i16(p1:i16, p2:i16)   returns (bool);");
	D("function {:bvbuiltin \"bvsle\"}   $sle.i16(p1:i16, p2:i16)   returns (bool);");
	D("function {:bvbuiltin \"bvslt\"}   $slt.i16(p1:i16, p2:i16)   returns (bool);");
	D("function {:bvbuiltin \"bvsge\"}   $sge.i16(p1:i16, p2:i16)   returns (bool);");
	D("function {:bvbuiltin \"bvsgt\"}   $sgt.i16(p1:i16, p2:i16)   returns (bool);");

	D("function {:bvbuiltin \"bvule\"}   $ule.i8(p1:i8, p2:i8)   returns (bool);");
	D("function {:bvbuiltin \"bvult\"}   $ult.i8(p1:i8, p2:i8)   returns (bool);");
	D("function {:bvbuiltin \"bvuge\"}   $uge.i8(p1:i8, p2:i8)   returns (bool);");
	D("function {:bvbuiltin \"bvugt\"}   $ugt.i8(p1:i8, p2:i8)   returns (bool);");
	D("function {:bvbuiltin \"bvsle\"}   $sle.i8(p1:i8, p2:i8)   returns (bool);");
	D("function {:bvbuiltin \"bvslt\"}   $slt.i8(p1:i8, p2:i8)   returns (bool);");
	D("function {:bvbuiltin \"bvsge\"}   $sge.i8(p1:i8, p2:i8)   returns (bool);");
	D("function {:bvbuiltin \"bvsgt\"}   $sgt.i8(p1:i8, p2:i8)   returns (bool);");

	D("function {:inline} $i2b(i: i32) returns (bool) {i != 0bv32}");
	D("function {:inline} $b2i(b: bool) returns (i32) {if b then 1bv32 else 0bv32}");
	#else
	D("function {:inline} $add(p1:int, p2:int) returns (int) {p1 + p2}");
	D("function {:inline} $sub(p1:int, p2:int) returns (int) {p1 - p2}");
	D("function {:inline} $mul(p1:int, p2:int) returns (int) {p1 * p2}");
	D("function {:builtin \"div\"} $sdiv(p1:int, p2:int) returns (int);");
	D("function {:builtin \"div\"} $udiv(p1:int, p2:int) returns (int);");
	D("function {:builtin \"rem\"} $srem(p1:int, p2:int) returns (int);");
	D("function {:builtin \"rem\"} $urem(p1:int, p2:int) returns (int);");
	D("function $and(p1:int, p2:int) returns (int);");
	D("axiom $and(0,0) == 0;");
	D("axiom $and(0,1) == 0;");
	D("axiom $and(1,0) == 0;");
	D("axiom $and(1,1) == 1;");
	D("function $or(p1:int, p2:int) returns (int);");
	D("axiom $or(0,0) == 0;");
	D("axiom $or(0,1) == 1;");
	D("axiom $or(1,0) == 1;");
	D("axiom $or(1,1) == 1;");
	D("function $xor(p1:int, p2:int) returns (int);");
	D("axiom $xor(0,0) == 0;");
	D("axiom $xor(0,1) == 1;");
	D("axiom $xor(1,0) == 1;");
	D("axiom $xor(1,1) == 0;");
	D("function $lshr(p1:int, p2:int) returns (int);");
	D("function $ashr(p1:int, p2:int) returns (int);");
	D("function $shl(p1:int, p2:int) returns (int);");
	D("function {:inline} $ult(p1:int, p2:int) returns (bool) {p1 < p2}");
	D("function {:inline} $ugt(p1:int, p2:int) returns (bool) {p1 > p2}");
	D("function {:inline} $ule(p1:int, p2:int) returns (bool) {p1 <= p2}");
	D("function {:inline} $uge(p1:int, p2:int) returns (bool) {p1 >= p2}");
	D("function {:inline} $slt(p1:int, p2:int) returns (bool) {p1 < p2}");
	D("function {:inline} $sgt(p1:int, p2:int) returns (bool) {p1 > p2}");
	D("function {:inline} $sle(p1:int, p2:int) returns (bool) {p1 <= p2}");
	D("function {:inline} $sge(p1:int, p2:int) returns (bool) {p1 >= p2}");
	D("function $nand(p1:int, p2:int) returns (int);");
	D("function {:inline} $max(p1:int, p2:int) returns (int) {if p1 > p2 then p1 else p2}");
	D("function {:inline} $min(p1:int, p2:int) returns (int) {if p1 > p2 then p2 else p1}");
	D("function {:inline} $umax(p1:int, p2:int) returns (int) {if p1 > p2 then p1 else p2}");
	D("function {:inline} $umin(p1:int, p2:int) returns (int) {if p1 > p2 then p2 else p1}");
	D("function {:inline} $i2b(i: int) returns (bool) {i != 0}");
	D("function {:inline} $b2i(b: bool) returns (int) {if b then 1 else 0}");
	#endif
	// Floating point
	D("type float;");
	D("function $fp(ipart:int, fpart:int, epart:int) returns (float);");
	D("function $fadd(f1:float, f2:float) returns (float);");
	D("function $fsub(f1:float, f2:float) returns (float);");
	D("function $fmul(f1:float, f2:float) returns (float);");
	D("function $fdiv(f1:float, f2:float) returns (float);");
	D("function $frem(f1:float, f2:float) returns (float);");
  D("function $ffalse(f1:float, f2:float) returns (bool);");
  D("function $ftrue(f1:float, f2:float) returns (bool);");
	D("function $foeq(f1:float, f2:float) returns (bool);");
	D("function $foge(f1:float, f2:float) returns (bool);");
	D("function $fogt(f1:float, f2:float) returns (bool);");
	D("function $fole(f1:float, f2:float) returns (bool);");
	D("function $folt(f1:float, f2:float) returns (bool);");
	D("function $fone(f1:float, f2:float) returns (bool);");
	D("function $ford(f1:float, f2:float) returns (bool);");
	D("function $fueq(f1:float, f2:float) returns (bool);");
	D("function $fuge(f1:float, f2:float) returns (bool);");
	D("function $fugt(f1:float, f2:float) returns (bool);");
	D("function $fule(f1:float, f2:float) returns (bool);");
	D("function $fult(f1:float, f2:float) returns (bool);");
	D("function $fune(f1:float, f2:float) returns (bool);");
	D("function $funo(f1:float, f2:float) returns (bool);");
	D("function $fp2si(f:float) returns (int);");
	D("function $fp2ui(f:float) returns (int);");
	D("function $si2fp(i:int) returns (float);");
	D("function $ui2fp(i:int) returns (float);");

	D("axiom (forall f1, f2: float :: f1 != f2 || $foeq(f1,f2));");
	D("axiom (forall i: int :: $fp2ui($ui2fp(i)) == i);");
	D("axiom (forall f: float :: $ui2fp($fp2ui(f)) == f);");
	D("axiom (forall i: int :: $fp2si($si2fp(i)) == i);");
	D("axiom (forall f: float :: $si2fp($fp2si(f)) == f);");

	// Bit vectors
	#ifdef BITVECTOR
	D("type i8 = bv8;");
	D("type i16 = bv16;");
	D("type i32 = bv32;");
	D("type i64 = bv32;");
	D("type ref = i64;");
	#endif

	// Memory Model
	D("const $UNDEF: int;");
#ifdef BITVECTOR
	D("function $base(ref) returns (ref);");
	D("const unique $NULL: ref;");
	D("axiom $NULL == 0bv32;");
	D("function {:inline} $pa(pointer: ref, index: ref, size: ref) returns (ref) {$add.i32(pointer, $mul.i32(index, size))}");
	D("function {:inline} $b2p(b: bool) returns (ref) {if b then 1bv32 else 0bv32}");
	// Load
	D("function {:inline} $load.i64(M:[ref]i8, p:ref) returns (i64){M[$add.i32(p, 3bv32)]++M[$add.i32(p, 2bv32)]++M[$add.i32(p, 1bv32)]++M[p]}");
	D("function {:inline} $load.i32(M:[ref]i8, p:ref) returns (i32){M[$add.i32(p, 3bv32)]++M[$add.i32(p, 2bv32)]++M[$add.i32(p, 1bv32)]++M[p]}");
	D("function {:inline} $load.i16(M:[ref]i8, p:ref) returns (i16){M[$add.i32(p, 1bv32)]++M[p]}");
	D("function {:inline} $load.i8(M:[ref]i8, p:ref) returns (i8){M[p]}");
	// Shaobo: temporary representation for aggregate
	D("function {:inline} $load.i0(M:[ref]i8, p:ref) returns (i64){M[$add.i32(p, 3bv32)]++M[$add.i32(p, 2bv32)]++M[$add.i32(p, 1bv32)]++M[p]}");
	//D("function {:inline} $load.i8(M:[ref]i8, p:ref) returns (i8){M[p]}");
	//D("function {:inline} $load.i16(M:[ref]i8, p:ref) returns (i16){M[p]}");
	//D("function {:inline} $load.i32(M:[ref]i8, p:ref) returns (i32){M[p]}");
	//D("function {:inline} $load.i64(M:[ref]i8, p:ref) returns (ref){M[p]}");

	// Store
	D("function {:inline} $store.i64(M:[ref]i8, p:ref, v:i64) returns ([ref]i8) {M[p := v[8:0]][$add.i32(p, 1bv32) := v[16:8]][$add.i32(p, 2bv32) := v[24:16]][$add.i32(p, 3bv32) := v[32:24]]}");
	D("function {:inline} $store.i32(M:[ref]i8, p:ref, v:i32) returns ([ref]i8) {M[p := v[8:0]][$add.i32(p, 1bv32) := v[16:8]][$add.i32(p, 2bv32) := v[24:16]][$add.i32(p, 3bv32) := v[32:24]]}");
	D("function {:inline} $store.i16(M:[ref]i8, p:ref, v:i16) returns ([ref]i8) {M[p := v[8:0]][$add.i32(p, 1bv32) := v[16:8]]}");
	D("function {:inline} $store.i8(M:[ref]i8, p:ref, v:i8) returns ([ref]i8) {M[p := v]}");
	// Shaobo: temporary representation for aggregate
	D("function {:inline} $store.i0(M:[ref]i8, p:ref, v:i64) returns ([ref]i8) {M[p := v[8:0]][$add.i32(p, 1bv32) := v[16:8]][$add.i32(p, 2bv32) := v[24:16]][$add.i32(p, 3bv32) := v[32:24]]}");
	//D("function {:inline} $store.i8(M:[ref]i8, p:ref, v:i8) returns ([ref]i8) {M[p := v]}");
	//D("function {:inline} $store.i16(M:[ref]i8, p:ref, v:i8) returns ([ref]i8) {M[p := v]}");
	//D("function {:inline} $store.i32(M:[ref]i8, p:ref, v:i8) returns ([ref]i8) {M[p := v]}");
	//D("function {:inline} $store.i64(M:[ref]i8, p:ref, v:i8) returns ([ref]i8) {M[p := v]}");

	// Cast
	// Truncate
	D("function {:inline} $trunc.i64i32(p: i64) returns (i32) {p[32:0]}");
	D("function {:inline} $trunc.i64i16(p: i64) returns (i16) {p[16:0]}");
	D("function {:inline} $trunc.i64i8(p: i64) returns (i8) {p[8:0]}");
	D("function {:inline} $trunc.i32i16(p: i32) returns (i16) {p[16:0]}");
	D("function {:inline} $trunc.i32i8(p: i32) returns (i8) {p[8:0]}");
	D("function {:inline} $trunc.i16i8(p: i16) returns (i8) {p[8:0]}");
	// Zext
	D("function {:inline} $zext.i8i64(p: i8) returns (i64) {(0bv24)++p}");
	D("function {:inline} $zext.i8i32(p: i8) returns (i32) {(0bv24)++p}");
	D("function {:inline} $zext.i8i16(p: i8) returns (i16) {(0bv8)++p}");
	D("function {:inline} $zext.i16i64(p: i16) returns (i64) {(0bv16)++p}");
	D("function {:inline} $zext.i16i32(p: i16) returns (i32) {(0bv16)++p}");
	D("function {:inline} $zext.i32i64(p: i32) returns (i64) {p}");
	// Sext
	D("function {:inline} $sext.i8i64(p: i8) returns (i64) {if $sge.i8(p, 0bv8) then $zext.i8i64(p) else (($neg.i32(1bv32))[32:8])++p}");
	D("function {:inline} $sext.i8i32(p: i8) returns (i32) {if $sge.i8(p, 0bv8) then $zext.i8i32(p) else (($neg.i32(1bv32))[32:8])++p}");
	D("function {:inline} $sext.i8i16(p: i8) returns (i16) {if $sge.i8(p, 0bv8) then $zext.i8i16(p) else $neg.i8(1bv8)++p}");
	D("function {:inline} $sext.i16i64(p: i16) returns (i64) {if $sge.i16(p, 0bv16) then $zext.i16i64(p) else $neg.i16(1bv16)++p}");
	D("function {:inline} $sext.i16i32(p: i16) returns (i32) {if $sge.i16(p, 0bv16) then $zext.i16i32(p) else $neg.i16(1bv16)++p}");
	D("function {:inline} $sext.i32i64(p: i32) returns (i64) {p}");

	D("function {:inline} $p2i(p: ref) returns (i64) {p}");
	D("function {:inline} $i2p(p: i64) returns (ref) {p}");
	D("function {:inline} $p2b(p: ref) returns (bool) {p != 0bv32}");
#else
	D("function $base(int) returns (int);");
	D("const unique $NULL: int;");
	D("axiom $NULL == 0;");
	D("function {:inline} $pa(pointer: int, index: int, size: int) returns (int) {pointer + index * size}");
	D("function {:inline} $b2p(b: bool) returns (int) {if b then 1 else 0}");
	D("function {:inline} $p2i(p: int) returns (int) {p}");
	D("function {:inline} $i2p(p: int) returns (int) {p}");
	D("function {:inline} $p2b(p: int) returns (bool) {p != 0}");
#endif
	D("function {:inline} $trunc(p: int, size: int) returns (int) {p}");

	// Memory debugging symbols
	D("type $mop;");
	D("procedure boogie_si_record_mop(m: $mop);");
  D("procedure boogie_si_record_bool(b: bool);");
#ifdef BITVECTOR
	D("procedure boogie_si_record_i8(i: i8);");
	D("procedure boogie_si_record_i16(i: i16);");
	D("procedure boogie_si_record_i32(i: i32);");
	D("procedure boogie_si_record_i64(i: i64);");
#else
	D("procedure boogie_si_record_int(i: int);");
  D("procedure boogie_si_record_float(f: float);");
	D("procedure boogie_si_record_float(f: float);");
	D("const $MOP: $mop;");

#ifdef BITVECTOR
	D("const $GLOBALS_BOTTOM: ref;");
	D("function {:inline} $isExternal(p: ref) returns (bool) { $slt.i32(p, $sub.i32($GLOBALS_BOTTOM, 32768bv32)) }");
#else
	D("const $GLOBALS_BOTTOM: int;");
	D("function {:inline} $isExternal(p: int) returns (bool) { p < $GLOBALS_BOTTOM - 32768 }");
#endif

#if MEMORY_MODEL_NO_REUSE_IMPLS
#ifdef BITVECTOR
	D("var $Alloc: [ref] bool;");
	D("var $CurrAddr:ref;");

	D("procedure $malloc(n: i32) returns (p: ref)\n"
			"modifies $CurrAddr, $Alloc;\n"
			"{\n"
			"  assume $ugt.i32($CurrAddr, 0bv32);\n"
			"  p := $CurrAddr;\n"
			"  if ($ugt.i32(n, 0bv32)) {\n"
			"    $CurrAddr := $add.i32($CurrAddr, n);\n"
			"  } else {\n"
			"    $CurrAddr := $add.i32($CurrAddr, 1bv32);\n"
			"  }\n"
			"  $Alloc[p] := true;\n"
			"}");

	D("procedure $free(p: ref)\n"
			"modifies $Alloc;\n"
			"{\n"
			"  $Alloc[p] := false;\n"
			"}");

	D("procedure $alloca(n: i32) returns (p: ref)\n"
			"modifies $CurrAddr, $Alloc;\n"
			"{\n"
			"  assume $ugt.i32($CurrAddr, 0bv32);\n"
			"  p := $CurrAddr;\n"
			"  if ($ugt.i32(n, 0bv32)) {\n"
			"    $CurrAddr := $add.i32($CurrAddr, n);\n"
			"  } else {\n"
			"    $CurrAddr := $add.i32($CurrAddr, 1bv32);\n"
			"  }\n"
			"  $Alloc[p] := true;\n"
			"}");
#else
	D("var $Alloc: [int] bool;");
	D("var $CurrAddr:int;");

	D("procedure $malloc(n: int) returns (p: int)\n"
			"modifies $CurrAddr, $Alloc;\n"
			"{\n"
			"  assume $CurrAddr > 0;\n"
			"  p := $CurrAddr;\n"
			"  if (n > 0) {\n"
			"    $CurrAddr := $CurrAddr + n;\n"
			"  } else {\n"
			"    $CurrAddr := $CurrAddr + 1;\n"
			"  }\n"
			"  $Alloc[p] := true;\n"
			"}");

	D("procedure $free(p: int)\n"
			"modifies $Alloc;\n"
			"{\n"
			"  $Alloc[p] := false;\n"
			"}");

	D("procedure $alloca(n: int) returns (p: int)\n"
			"modifies $CurrAddr, $Alloc;\n"
			"{\n"
			"  assume $CurrAddr > 0;\n"
			"  p := $CurrAddr;\n"
			"  if (n > 0) {\n"
			"    $CurrAddr := $CurrAddr + n;\n"
			"  } else {\n"
			"    $CurrAddr := $CurrAddr + 1;\n"
			"  }\n"
			"  $Alloc[p] := true;\n"
			"}");
#endif

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
#ifdef BITVECTOR
	D("var $Alloc: [ref] bool;");
	D("var $Size: [ref] i32;");

	D("procedure $malloc(n: i32) returns (p: ref);\n"
			"modifies $Alloc, $Size;\n"
			"ensures $ugt(p, 0bv32);\n"
			"ensures !old($Alloc[p]);\n"
			"ensures (forall q: ref :: old($Alloc[q]) ==> ($ult($add(p, n), q) || $ugt(p, $add(q, $Size[q]))));\n"
			"ensures $Alloc[p];\n"
			"ensures $Size[p] == n;\n"
			"ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
			"ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
			"ensures $uge(n, 0bv32) ==> (forall q: ref :: {$base(q)} $ule(p, q) && $ult(q, $add(p, n)) ==> $base(q) == p);");

	D("procedure $free(p: ref);\n"
			"modifies $Alloc;\n"
			"ensures !$Alloc[p];\n"
			"ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));");

	D("procedure $alloca(n: i32) returns (p: ref);\n"
			"modifies $Alloc, $Size;\n"
			"ensures $ugt(p, 0bv32);\n"
			"ensures !old($Alloc[p]);\n"
			"ensures (forall q: ref :: old($Alloc[q]) ==> ($ult($add(p, n), q) || $ugt(p, $add(q, $Size[q]))));\n"
			"ensures $Alloc[p];\n"
			"ensures $Size[p] == n;\n"
			"ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
			"ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
			"ensures $uge(n, 0bv32) ==> (forall q: ref :: {$base(q)} $ule(p, q) && $ult(q, $add(p, n)) ==> $base(q) == p);");
#else
	D("var $Alloc: [int] bool;");
	D("var $Size: [int] int;");

	D("procedure $malloc(n: int) returns (p: int);\n"
			"modifies $Alloc, $Size;\n"
			"ensures p > 0;\n"
			"ensures !old($Alloc[p]);\n"
			"ensures (forall q: int :: old($Alloc[q]) ==> (p + n < q || p > q + $Size[q]));\n"
			"ensures $Alloc[p];\n"
			"ensures $Size[p] == n;\n"
			"ensures (forall q: int :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
			"ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
			"ensures n >= 0 ==> (forall q: int :: {$base(q)} p <= q && q < p+n ==> $base(q) == p);");

	D("procedure $free(p: int);\n"
			"modifies $Alloc;\n"
			"ensures !$Alloc[p];\n"
			"ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));");

	D("procedure $alloca(n: int) returns (p: int);\n"
			"modifies $Alloc, $Size;\n"
			"ensures p > 0;\n"
			"ensures !old($Alloc[p]);\n"
			"ensures (forall q: int :: old($Alloc[q]) ==> (p + n < q || p > q + $Size[q]));\n"
			"ensures $Alloc[p];\n"
			"ensures $Size[p] == n;\n"
			"ensures (forall q: int :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
			"ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
			"ensures n >= 0 ==> (forall q: int :: {$base(q)} p <= q && q < p+n ==> $base(q) == p);");
#endif

#else // NO_REUSE does not reuse previously-allocated addresses
#ifdef BITVECTOR
	D("var $Alloc: [ref] bool;");
	D("var $CurrAddr:ref;");
	D("procedure $malloc(n: i32) returns (p: ref);\n"
			"modifies $CurrAddr, $Alloc;\n"
			"ensures $sgt(p, 0bv32);\n"
			"ensures p == old($CurrAddr);\n"
			"ensures $ugt($CurrAddr, old($CurrAddr));\n"
			"ensures $uge(n, 0bv32) ==> $uge($CurrAddr, $add(old($CurrAddr), n));\n"
			"ensures $Alloc[p];\n"
			"ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
			"ensures $uge(n, 0bv32) ==> (forall q: ref :: {$base(q)} $ule(p, q) && $ult(q, $add(p, n)) ==> $base(q) == p);");

	D("procedure $free(p: ref);\n"
			"modifies $Alloc;\n"
			"ensures !$Alloc[p];\n"
			"ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));");

	D("procedure $alloca(n: i32) returns (p: ref);\n"
			"modifies $CurrAddr, $Alloc;\n"
			"ensures $sgt(p, 0bv32);\n"
			"ensures p == old($CurrAddr);\n"
			"ensures $ugt($CurrAddr, old($CurrAddr));\n"
			"ensures $uge(n, 0bv32) ==> $uge($CurrAddr, $add(old($CurrAddr), n));\n"
			"ensures $Alloc[p];\n"
			"ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
			"ensures $uge(n, 0bv32) ==> (forall q: ref :: {$base(q)} $ule(p, q) && $ult(q, $add(p, n)) ==> $base(q) == p);");
#else
	D("var $Alloc: [int] bool;");
	D("var $CurrAddr:int;");
	D("procedure $malloc(n: int) returns (p: int);\n"
			"modifies $CurrAddr, $Alloc;\n"
			"ensures p > 0;\n"
			"ensures p == old($CurrAddr);\n"
			"ensures $CurrAddr > old($CurrAddr);\n"
			"ensures n >= 0 ==> $CurrAddr >= old($CurrAddr) + n;\n"
			"ensures $Alloc[p];\n"
			"ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
			"ensures n >= 0 ==> (forall q: int :: {$base(q)} p <= q && q < p+n ==> $base(q) == p);");

	D("procedure $free(p: int);\n"
			"modifies $Alloc;\n"
			"ensures !$Alloc[p];\n"
			"ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));");

	D("procedure $alloca(n: int) returns (p: int);\n"
			"modifies $CurrAddr, $Alloc;\n"
			"ensures p > 0;\n"
			"ensures p == old($CurrAddr);\n"
			"ensures $CurrAddr > old($CurrAddr);\n"
			"ensures n >= 0 ==> $CurrAddr >= old($CurrAddr) + n;\n"
			"ensures $Alloc[p];\n"
			"ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
			"ensures n >= 0 ==> (forall q: int :: {$base(q)} p <= q && q < p+n ==> $base(q) == p);");
#endif
#endif

  D("var $exn: bool;");
  D("var $exnv: int;");
  D("function $extractvalue(p: int, i: int) returns (int);");

  D("var $exn: bool;");
  D("var $exnv: int;");
  D("function $extractvalue(p: int, i: int) returns (int);");

#undef D
}

#ifdef __cplusplus
}
#endif

#endif /*SMACK_H_*/
