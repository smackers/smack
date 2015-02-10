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
  D("function {:bvbuiltin \"bvneg\"} $neg.i64(p1:i64) returns (i64);");
  D("function {:bvbuiltin \"bvadd\"} $add.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvsub\"} $sub.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvmul\"} $mul.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvshl\"} $shl.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvudiv\"} $udiv.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvsdiv\"} $sdiv.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvsmod\"} $smod.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvsrem\"} $srem.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvurem\"} $urem.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvlshr\"} $lshr.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvashr\"} $ashr.i64(p1:i64, p2:i64) returns (i64);");

  D("function {:bvbuiltin \"bvneg\"} $neg.i32(p1:i32) returns (i32);");
  D("function {:bvbuiltin \"bvadd\"} $add.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvsub\"} $sub.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvmul\"} $mul.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvshl\"} $shl.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvudiv\"} $udiv.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvsdiv\"} $sdiv.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvsmod\"} $smod.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvsrem\"} $srem.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvurem\"} $urem.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvlshr\"} $lshr.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvashr\"} $ashr.i32(p1:i32, p2:i32) returns (i32);");

  D("function {:bvbuiltin \"bvneg\"} $neg.i16(p1:i16) returns (i16);");
  D("function {:bvbuiltin \"bvadd\"} $add.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvsub\"} $sub.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvmul\"} $mul.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvshl\"} $shl.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvudiv\"} $udiv.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvsdiv\"} $sdiv.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvsmod\"} $smod.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvsrem\"} $srem.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvurem\"} $urem.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvlshr\"} $lshr.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvashr\"} $ashr.i16(p1:i16, p2:i16) returns (i16);");

  D("function {:bvbuiltin \"bvneg\"} $neg.i8(p1:i8) returns (i8);");
  D("function {:bvbuiltin \"bvadd\"} $add.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvsub\"} $sub.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvmul\"} $mul.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvshl\"} $shl.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvudiv\"} $udiv.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvsdiv\"} $sdiv.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvsmod\"} $smod.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvsrem\"} $srem.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvurem\"} $urem.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvlshr\"} $lshr.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvashr\"} $ashr.i8(p1:i8, p2:i8) returns (i8);");
  // Bitwise operations
  D("function {:bvbuiltin \"bvnot\"} $not.i64(p1:i64) returns (i64);");
  D("function {:bvbuiltin \"bvand\"} $and.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvor\"} $or.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:bvbuiltin \"bvxor\"} $xor.i64(p1:i64, p2:i64) returns (i64);");

  D("function {:bvbuiltin \"bvnot\"} $not.i32(p1:i32) returns (i32);");
  D("function {:bvbuiltin \"bvand\"} $and.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvor\"} $or.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:bvbuiltin \"bvxor\"} $xor.i32(p1:i32, p2:i32) returns (i32);");

  D("function {:bvbuiltin \"bvnot\"} $not.i16(p1:i16) returns (i16);");
  D("function {:bvbuiltin \"bvand\"} $and.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvor\"} $or.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:bvbuiltin \"bvxor\"} $xor.i16(p1:i16, p2:i16) returns (i16);");

  D("function {:bvbuiltin \"bvnot\"} $not.i8(p1:i8) returns (i8);");
  D("function {:bvbuiltin \"bvand\"} $and.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvor\"} $or.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:bvbuiltin \"bvxor\"} $xor.i8(p1:i8, p2:i8) returns (i8);");

  D("function {:bvbuiltin \"bvnot\"} $not.i1(p1:i1) returns (i1);");
  D("function {:bvbuiltin \"bvand\"} $and.i1(p1:i1, p2:i1) returns (i1);");
  D("function {:bvbuiltin \"bvor\"} $or.i1(p1:i1, p2:i1) returns (i1);");
  D("function {:bvbuiltin \"bvxor\"} $xor.i1(p1:i1, p2:i1) returns (i1);");
  // Predicates
  D("function {:bvbuiltin \"bvule\"} $ule.i64(p1:i64, p2:i64) returns (bool);");
  D("function {:bvbuiltin \"bvult\"} $ult.i64(p1:i64, p2:i64) returns (bool);");
  D("function {:bvbuiltin \"bvuge\"} $uge.i64(p1:i64, p2:i64) returns (bool);");
  D("function {:bvbuiltin \"bvugt\"} $ugt.i64(p1:i64, p2:i64) returns (bool);");
  D("function {:bvbuiltin \"bvsle\"} $sle.i64(p1:i64, p2:i64) returns (bool);");
  D("function {:bvbuiltin \"bvslt\"} $slt.i64(p1:i64, p2:i64) returns (bool);");
  D("function {:bvbuiltin \"bvsge\"} $sge.i64(p1:i64, p2:i64) returns (bool);");
  D("function {:bvbuiltin \"bvsgt\"} $sgt.i64(p1:i64, p2:i64) returns (bool);");

  D("function {:bvbuiltin \"bvule\"} $ule.i32(p1:i32, p2:i32) returns (bool);");
  D("function {:bvbuiltin \"bvult\"} $ult.i32(p1:i32, p2:i32) returns (bool);");
  D("function {:bvbuiltin \"bvuge\"} $uge.i32(p1:i32, p2:i32) returns (bool);");
  D("function {:bvbuiltin \"bvugt\"} $ugt.i32(p1:i32, p2:i32) returns (bool);");
  D("function {:bvbuiltin \"bvsle\"} $sle.i32(p1:i32, p2:i32) returns (bool);");
  D("function {:bvbuiltin \"bvslt\"} $slt.i32(p1:i32, p2:i32) returns (bool);");
  D("function {:bvbuiltin \"bvsge\"} $sge.i32(p1:i32, p2:i32) returns (bool);");
  D("function {:bvbuiltin \"bvsgt\"} $sgt.i32(p1:i32, p2:i32) returns (bool);");

  D("function {:bvbuiltin \"bvule\"} $ule.i16(p1:i16, p2:i16) returns (bool);");
  D("function {:bvbuiltin \"bvult\"} $ult.i16(p1:i16, p2:i16) returns (bool);");
  D("function {:bvbuiltin \"bvuge\"} $uge.i16(p1:i16, p2:i16) returns (bool);");
  D("function {:bvbuiltin \"bvugt\"} $ugt.i16(p1:i16, p2:i16) returns (bool);");
  D("function {:bvbuiltin \"bvsle\"} $sle.i16(p1:i16, p2:i16) returns (bool);");
  D("function {:bvbuiltin \"bvslt\"} $slt.i16(p1:i16, p2:i16) returns (bool);");
  D("function {:bvbuiltin \"bvsge\"} $sge.i16(p1:i16, p2:i16) returns (bool);");
  D("function {:bvbuiltin \"bvsgt\"} $sgt.i16(p1:i16, p2:i16) returns (bool);");

  D("function {:bvbuiltin \"bvule\"} $ule.i8(p1:i8, p2:i8) returns (bool);");
  D("function {:bvbuiltin \"bvult\"} $ult.i8(p1:i8, p2:i8) returns (bool);");
  D("function {:bvbuiltin \"bvuge\"} $uge.i8(p1:i8, p2:i8) returns (bool);");
  D("function {:bvbuiltin \"bvugt\"} $ugt.i8(p1:i8, p2:i8) returns (bool);");
  D("function {:bvbuiltin \"bvsle\"} $sle.i8(p1:i8, p2:i8) returns (bool);");
  D("function {:bvbuiltin \"bvslt\"} $slt.i8(p1:i8, p2:i8) returns (bool);");
  D("function {:bvbuiltin \"bvsge\"} $sge.i8(p1:i8, p2:i8) returns (bool);");
  D("function {:bvbuiltin \"bvsgt\"} $sgt.i8(p1:i8, p2:i8) returns (bool);");

  D("type i1 = bv1;")
  D("function {:inline} $i2b(i: i1) returns (bool) {i != 0bv1}");
  D("function {:inline} $b2i(b: bool) returns (i1) {if b then 1bv1 else 0bv1}");
#else
  D("function {:inline} $add.i64(p1:i64, p2:i64) returns (i64) {p1 + p2}");
  D("function {:inline} $sub.i64(p1:i64, p2:i64) returns (i64) {p1 - p2}");
  D("function {:inline} $mul.i64(p1:i64, p2:i64) returns (i64) {p1 * p2}");
  D("function {:inline} $neg.i64(p:i64) returns (i64) {0 - p}");
  D("function {:builtin \"div\"} $udiv.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:builtin \"div\"} $sdiv.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:buildin \"mod\"} $smod.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:buildin \"rem\"} $srem.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:buildin \"rem\"} $urem.i64(p1:i64, p2:i64) returns (i64);");
  D("function {:inline} $shl.i64(p1:i64, p2:i64) returns (i64){p1}");
  D("function {:inline} $lshr.i64(p1:i64, p2:i64) returns (i64){p1}");
  D("function {:inline} $ashr.i64(p1:i64, p2:i64) returns (i64){p1}");

  D("function {:inline} $add.i32(p1:i32, p2:i32) returns (i32) {p1 + p2}");
  D("function {:inline} $sub.i32(p1:i32, p2:i32) returns (i32) {p1 - p2}");
  D("function {:inline} $mul.i32(p1:i32, p2:i32) returns (i32) {p1 * p2}");
  D("function {:inline} $neg.i32(p:i32) returns (i32) {0 - p}");
  D("function {:builtin \"div\"} $udiv.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:builtin \"div\"} $sdiv.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:buildin \"mod\"} $smod.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:buildin \"rem\"} $srem.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:buildin \"rem\"} $urem.i32(p1:i32, p2:i32) returns (i32);");
  D("function {:inline} $shl.i32(p1:i32, p2:i32) returns (i32){p1}");
  D("function {:inline} $lshr.i32(p1:i32, p2:i32) returns (i32){p1}");
  D("function {:inline} $ashr.i32(p1:i32, p2:i32) returns (i32){p1}");

  D("function {:inline} $add.i16(p1:i16, p2:i16) returns (i16) {p1 + p2}");
  D("function {:inline} $sub.i16(p1:i16, p2:i16) returns (i16) {p1 - p2}");
  D("function {:inline} $mul.i16(p1:i16, p2:i16) returns (i16) {p1 * p2}");
  D("function {:inline} $neg.i16(p:i16) returns (i16) {0 - p}");
  D("function {:builtin \"div\"} $udiv.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:builtin \"div\"} $sdiv.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:buildin \"mod\"} $smod.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:buildin \"rem\"} $srem.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:buildin \"rem\"} $urem.i16(p1:i16, p2:i16) returns (i16);");
  D("function {:inline} $shl.i16(p1:i16, p2:i16) returns (i16){p1}");
  D("function {:inline} $lshr.i16(p1:i16, p2:i16) returns (i16){p1}");
  D("function {:inline} $ashr.i16(p1:i16, p2:i16) returns (i16){p1}");

  D("function {:inline} $add.i8(p1:i8, p2:i8) returns (i8) {p1 + p2}");
  D("function {:inline} $sub.i8(p1:i8, p2:i8) returns (i8) {p1 - p2}");
  D("function {:inline} $mul.i8(p1:i8, p2:i8) returns (i8) {p1 * p2}");
  D("function {:inline} $neg.i8(p:i8) returns (i8) {0 - p}");
  D("function {:builtin \"div\"} $udiv.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:builtin \"div\"} $sdiv.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:buildin \"mod\"} $smod.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:buildin \"rem\"} $srem.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:buildin \"rem\"} $urem.i8(p1:i8, p2:i8) returns (i8);");
  D("function {:inline} $shl.i8(p1:i8, p2:i8) returns (i8){p1}");
  D("function {:inline} $lshr.i8(p1:i8, p2:i8) returns (i8){p1}");
  D("function {:inline} $ashr.i8(p1:i8, p2:i8) returns (i8){p1}");

  D("function $and.i64(p64:i64, p2:i64) returns (i64);");
  D("function $or.i64(p64:i64, p2:i64) returns (i64);");
  D("function $xor.i64(p64:i64, p2:i64) returns (i64);");

  D("function $and.i32(p32:i32, p2:i32) returns (i32);");
  D("function $or.i32(p32:i32, p2:i32) returns (i32);");
  D("function $xor.i32(p32:i32, p2:i32) returns (i32);");

  D("function $and.i16(p16:i16, p2:i16) returns (i16);");
  D("function $or.i16(p16:i16, p2:i16) returns (i16);");
  D("function $xor.i16(p16:i16, p2:i16) returns (i16);");

  D("function $and.i8(p8:i8, p2:i8) returns (i8);");
  D("function $or.i8(p8:i8, p2:i8) returns (i8);");
  D("function $xor.i8(p8:i8, p2:i8) returns (i8);");

  D("function $and.i1(p1:i1, p2:i1) returns (i1);");
  D("axiom $and.i1(0,0) == 0;");
  D("axiom $and.i1(0,1) == 0;");
  D("axiom $and.i1(1,0) == 0;");
  D("axiom $and.i1(1,1) == 1;");
  D("function $or.i1(p1:i1, p2:i1) returns (i1);");
  D("axiom $or.i1(0,0) == 0;");
  D("axiom $or.i1(0,1) == 1;");
  D("axiom $or.i1(1,0) == 1;");
  D("axiom $or.i1(1,1) == 1;");
  D("function $xor.i1(p1:i1, p2:i1) returns (i1);");
  D("axiom $xor.i1(0,0) == 0;");
  D("axiom $xor.i1(0,1) == 1;");
  D("axiom $xor.i1(1,0) == 1;");
  D("axiom $xor.i1(1,1) == 0;");

  // Predicates
  D("function {:inline} $ult.i64(p1:i64, p2:i64) returns (bool) {p1 < p2}");
  D("function {:inline} $ugt.i64(p1:i64, p2:i64) returns (bool) {p1 > p2}");
  D("function {:inline} $ule.i64(p1:i64, p2:i64) returns (bool) {p1 <= p2}");
  D("function {:inline} $uge.i64(p1:i64, p2:i64) returns (bool) {p1 >= p2}");
  D("function {:inline} $slt.i64(p1:i64, p2:i64) returns (bool) {p1 < p2}");
  D("function {:inline} $sgt.i64(p1:i64, p2:i64) returns (bool) {p1 > p2}");
  D("function {:inline} $sle.i64(p1:i64, p2:i64) returns (bool) {p1 <= p2}");
  D("function {:inline} $sge.i64(p1:i64, p2:i64) returns (bool) {p1 >= p2}");

  D("function {:inline} $ult.i32(p1:i32, p2:i32) returns (bool) {p1 < p2}");
  D("function {:inline} $ugt.i32(p1:i32, p2:i32) returns (bool) {p1 > p2}");
  D("function {:inline} $ule.i32(p1:i32, p2:i32) returns (bool) {p1 <= p2}");
  D("function {:inline} $uge.i32(p1:i32, p2:i32) returns (bool) {p1 >= p2}");
  D("function {:inline} $slt.i32(p1:i32, p2:i32) returns (bool) {p1 < p2}");
  D("function {:inline} $sgt.i32(p1:i32, p2:i32) returns (bool) {p1 > p2}");
  D("function {:inline} $sle.i32(p1:i32, p2:i32) returns (bool) {p1 <= p2}");
  D("function {:inline} $sge.i32(p1:i32, p2:i32) returns (bool) {p1 >= p2}");

  D("function {:inline} $ult.i16(p1:i16, p2:i16) returns (bool) {p1 < p2}");
  D("function {:inline} $ugt.i16(p1:i16, p2:i16) returns (bool) {p1 > p2}");
  D("function {:inline} $ule.i16(p1:i16, p2:i16) returns (bool) {p1 <= p2}");
  D("function {:inline} $uge.i16(p1:i16, p2:i16) returns (bool) {p1 >= p2}");
  D("function {:inline} $slt.i16(p1:i16, p2:i16) returns (bool) {p1 < p2}");
  D("function {:inline} $sgt.i16(p1:i16, p2:i16) returns (bool) {p1 > p2}");
  D("function {:inline} $sle.i16(p1:i16, p2:i16) returns (bool) {p1 <= p2}");
  D("function {:inline} $sge.i16(p1:i16, p2:i16) returns (bool) {p1 >= p2}");

  D("function {:inline} $ult.i8(p1:i8, p2:i8) returns (bool) {p1 < p2}");
  D("function {:inline} $ugt.i8(p1:i8, p2:i8) returns (bool) {p1 > p2}");
  D("function {:inline} $ule.i8(p1:i8, p2:i8) returns (bool) {p1 <= p2}");
  D("function {:inline} $uge.i8(p1:i8, p2:i8) returns (bool) {p1 >= p2}");
  D("function {:inline} $slt.i8(p1:i8, p2:i8) returns (bool) {p1 < p2}");
  D("function {:inline} $sgt.i8(p1:i8, p2:i8) returns (bool) {p1 > p2}");
  D("function {:inline} $sle.i8(p1:i8, p2:i8) returns (bool) {p1 <= p2}");
  D("function {:inline} $sge.i8(p1:i8, p2:i8) returns (bool) {p1 >= p2}");

  D("type i1 = int;")
  D("function {:inline} $i2b(i: i1) returns (bool) {i != 0}");
  D("function {:inline} $b2i(b: bool) returns (i8) {if b then 1 else 0}");

  D("function {:inline} $trunc.i64.i32(p: i64) returns (i32) {p}");
  D("function {:inline} $trunc.i64.i16(p: i64) returns (i16) {p}");
  D("function {:inline} $trunc.i64.i8(p: i64) returns (i8) {p}");
  D("function {:inline} $trunc.i64.i1(p: i64) returns (i1) {p}");
  D("function {:inline} $trunc.i32.i16(p: i32) returns (i16) {p}");
  D("function {:inline} $trunc.i32.i8(p: i32) returns (i8) {p}");
  D("function {:inline} $trunc.i32.i1(p: i32) returns (i1) {p}");
  D("function {:inline} $trunc.i16.i8(p: i16) returns (i8) {p}");
  D("function {:inline} $trunc.i16.i1(p: i16) returns (i1) {p}");
  D("function {:inline} $trunc.i8.i1(p: i8) returns (i1) {p}");

  D("function {:inline} $zext.i1.i64(p: i1) returns (i64) {p}");
  D("function {:inline} $zext.i1.i32(p: i1) returns (i32) {p}");
  D("function {:inline} $zext.i1.i16(p: i1) returns (i16) {p}");
  D("function {:inline} $zext.i1.i8(p: i1) returns (i8) {p}");
  D("function {:inline} $zext.i8.i64(p: i8) returns (i64) {p}");
  D("function {:inline} $zext.i8.i32(p: i8) returns (i32) {p}");
  D("function {:inline} $zext.i8.i16(p: i8) returns (i16) {p}");
  D("function {:inline} $zext.i16.i64(p: i16) returns (i64) {p}");
  D("function {:inline} $zext.i16.i32(p: i16) returns (i32) {p}");
  D("function {:inline} $zext.i32.i64(p: i32) returns (i64) {p}");

  D("function {:inline} $sext.i1.i64(p: i1) returns (i64) {p}");
  D("function {:inline} $sext.i1.i32(p: i1) returns (i32) {p}");
  D("function {:inline} $sext.i1.i16(p: i1) returns (i16) {p}");
  D("function {:inline} $sext.i1.i8(p: i1) returns (i8) {p}");
  D("function {:inline} $sext.i8.i64(p: i8) returns (i64) {p}");
  D("function {:inline} $sext.i8.i32(p: i8) returns (i32) {p}");
  D("function {:inline} $sext.i8.i16(p: i8) returns (i16) {p}");
  D("function {:inline} $sext.i16.i64(p: i16) returns (i64) {p}");
  D("function {:inline} $sext.i16.i32(p: i16) returns (i32) {p}");
  D("function {:inline} $sext.i32.i64(p: i32) returns (i64) {p}");

  D("function $nand(p1:int, p2:int) returns (int);");
  D("function {:inline} $max(p1:int, p2:int) returns (int) {if p1 > p2 then p1 else p2}");
  D("function {:inline} $min(p1:int, p2:int) returns (int) {if p1 > p2 then p2 else p1}");
  D("function {:inline} $umax(p1:int, p2:int) returns (int) {if p1 > p2 then p1 else p2}");
  D("function {:inline} $umin(p1:int, p2:int) returns (int) {if p1 > p2 then p2 else p1}");
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

  D("axiom (forall f1, f2: float :: f1 != f2 || $foeq(f1,f2));");
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
  D("const $UNDEF: ref;");
  D("function $base(ref) returns (ref);");
  D("const unique $NULL: ref;");
  D("const unique $REF_CONST_1: ref;");
  D("const unique $REF_CONST_2: ref;");
  D("const unique $REF_CONST_3: ref;");
  D("const unique $REF_CONST_4: ref;");
  D("const unique $REF_CONST_5: ref;");
  D("const unique $REF_CONST_6: ref;");
  D("const unique $REF_CONST_7: ref;");
  D("function {:inline} $b2p(b: bool) returns (ref) {if b then $REF_CONST_1 else $NULL}");
  D("function {:inline} $p2b(p: ref) returns (bool) {p != $NULL}");
#ifdef BITVECTOR
  //Pointer Arithmetic
  D("function {:bvbuiltin \"bvadd\"} $add.ref(p1:ref, p2:ref) returns (ref);");
  D("function {:bvbuiltin \"bvsub\"} $sub.ref(p1:ref, p2:ref) returns (ref);");
  D("function {:bvbuiltin \"bvmul\"} $mul.ref(p1:ref, p2:ref) returns (ref);");
  D("function {:bvbuiltin \"bvult\"} $ult.ref(p1:ref, p2:ref) returns (bool);");
  D("function {:bvbuiltin \"bvugt\"} $ugt.ref(p1:ref, p2:ref) returns (bool);");
  D("function {:bvbuiltin \"bvule\"} $ule.ref(p1:ref, p2:ref) returns (bool);");
  D("function {:bvbuiltin \"bvuge\"} $uge.ref(p1:ref, p2:ref) returns (bool);");
  D("function {:bvbuiltin \"bvslt\"} $slt.ref(p1:ref, p2:ref) returns (bool);");
  D("function {:bvbuiltin \"bvsgt\"} $sgt.ref(p1:ref, p2:ref) returns (bool);");
  D("function {:bvbuiltin \"bvsle\"} $sle.ref(p1:ref, p2:ref) returns (bool);");
  D("function {:bvbuiltin \"bvsge\"} $sge.ref(p1:ref, p2:ref) returns (bool);");


  D("function {:inline} $load.i64(M:[ref]i8, p:ref) returns (i64){$load.i32(M, $add.ref(p, $REF_CONST_4))++$load.i32(M, p)}");
  D("function {:inline} $load.i32(M:[ref]i8, p:ref) returns (i32){M[$add.ref(p, $REF_CONST_3)]++M[$add.ref(p, $REF_CONST_2)]++M[$add.ref(p, $REF_CONST_1)]++M[p]}");
  D("function {:inline} $load.i16(M:[ref]i8, p:ref) returns (i16){M[$add.ref(p, $REF_CONST_1)]++M[p]}");
  D("function {:inline} $load.i8(M:[ref]i8, p:ref) returns (i8){M[p]}");

  D("function {:inline} $store.i64(M:[ref]i8, p:ref, v:i64) returns ([ref]i8)"
    "{M[p := v[8:0]][$add.ref(p, $REF_CONST_1) := v[16:8]][$add.ref(p, $REF_CONST_2) := v[24:16]][$add.ref(p, $REF_CONST_3) := v[32:24]]"
    "[$add.ref(p, $REF_CONST_4) := v[40:32]][$add.ref(p, $REF_CONST_5) := v[48:40]][$add.ref(p, $REF_CONST_6) := v[56:48]][$add.ref(p, $REF_CONST_7) := v[64:56]]}");
  D("function {:inline} $store.i32(M:[ref]i8, p:ref, v:i32) returns ([ref]i8) {M[p := v[8:0]][$add.ref(p, $REF_CONST_1) := v[16:8]][$add.ref(p, $REF_CONST_2) := v[24:16]][$add.ref(p, $REF_CONST_3) := v[32:24]]}");
  D("function {:inline} $store.i16(M:[ref]i8, p:ref, v:i16) returns ([ref]i8) {M[p := v[8:0]][$add.ref(p, $REF_CONST_1) := v[16:8]]}");
  D("function {:inline} $store.i8(M:[ref]i8, p:ref, v:i8) returns ([ref]i8) {M[p := v]}");

  D("function {:inline} $isExternal(p: ref) returns (bool) {$slt.ref(p, $sub.ref($GLOBALS_BOTTOM, 32768bv64))}");
  D("function {:inline} $trunc.i64.i32(p: i64) returns (i32) {p[32:0]}");
  D("function {:inline} $trunc.i64.i16(p: i64) returns (i16) {p[16:0]}");
  D("function {:inline} $trunc.i64.i8(p: i64) returns (i8) {p[8:0]}");
  D("function {:inline} $trunc.i64.i1(p: i64) returns (i1) {if p != 0bv64 then 1bv1 else 0bv1}");
  D("function {:inline} $trunc.i32.i16(p: i32) returns (i16) {p[16:0]}");
  D("function {:inline} $trunc.i32.i8(p: i32) returns (i8) {p[8:0]}");
  D("function {:inline} $trunc.i32.i1(p: i32) returns (i1) {if p != 0bv32 then 1bv1 else 0bv1}");
  D("function {:inline} $trunc.i16.i8(p: i16) returns (i8) {p[8:0]}");
  D("function {:inline} $trunc.i8.i1(p: i8) returns (i1) {if p != 0bv8 then 1bv1 else 0bv1}");

  D("function {:inline} $zext.i1.i64(p: i1) returns (i64) {if p != 0bv1 then 1bv64 else 0bv64}");
  D("function {:inline} $zext.i1.i32(p: i1) returns (i32) {if p != 0bv1 then 1bv32 else 0bv32}");
  D("function {:inline} $zext.i1.i16(p: i1) returns (i16) {if p != 0bv1 then 1bv16 else 0bv16}");
  D("function {:inline} $zext.i1.i8(p: i1) returns (i8) {if p != 0bv1 then 1bv8 else 0bv8}");
  D("function {:inline} $zext.i8.i64(p: i8) returns (i64) {(0bv56)++p}");
  D("function {:inline} $zext.i8.i32(p: i8) returns (i32) {(0bv24)++p}");
  D("function {:inline} $zext.i8.i16(p: i8) returns (i16) {(0bv8)++p}");
  D("function {:inline} $zext.i16.i64(p: i16) returns (i64) {(0bv48)++p}");
  D("function {:inline} $zext.i16.i32(p: i16) returns (i32) {(0bv16)++p}");
  D("function {:inline} $zext.i32.i64(p: i32) returns (i64) {(0bv32)++p}");

  D("function {:inline} $sext.i1.i64(p: i1) returns (i64) {if p != 0bv1 then 1bv64 else 0bv64}");
  D("function {:inline} $sext.i1.i32(p: i1) returns (i32) {if p != 0bv1  then 1bv32 else 0bv32}");
  D("function {:inline} $sext.i1.i16(p: i1) returns (i16) {if p != 0bv1 then 1bv16 else 0bv16}");
  D("function {:inline} $sext.i1.i8(p: i1) returns (i8) {if p != 0bv1 then 1bv8 else 0bv8}");
  D("function {:inline} $sext.i8.i64(p: i8) returns (i64) {if $sge.i8(p, 0bv8) then $zext.i8.i64(p) else (($neg.i64(1bv64))[64:8])++p}");
  D("function {:inline} $sext.i8.i32(p: i8) returns (i32) {if $sge.i8(p, 0bv8) then $zext.i8.i32(p) else (($neg.i32(1bv32))[32:8])++p}");
  D("function {:inline} $sext.i8.i16(p: i8) returns (i16) {if $sge.i8(p, 0bv8) then $zext.i8.i16(p) else $neg.i8(1bv8)++p}");
  D("function {:inline} $sext.i16.i64(p: i16) returns (i64) {if $sge.i16(p, 0bv16) then $zext.i16.i64(p) else $neg.i64(1bv64)[64:16]++p}");
  D("function {:inline} $sext.i16.i32(p: i16) returns (i32) {if $sge.i16(p, 0bv16) then $zext.i16.i32(p) else $neg.i16(1bv16)++p}");
  D("function {:inline} $sext.i32.i64(p: i32) returns (i64) {if $sge.i32(p, 0bv32) then $zext.i32.i64(p) else $neg.i32(1bv32)++p}");
#else
  D("axiom $NULL == 0;");
  D("function {:inline} $add.ref(p1:ref, p2:ref) returns (ref) {p1 + p2}");
  D("function {:inline} $sub.ref(p1:ref, p2:ref) returns (ref) {p1 - p2}");
  D("function {:inline} $mul.ref(p1:ref, p2:ref) returns (ref) {p1 * p2}");
  D("function {:inline} $neg.ref(p:ref) returns (ref) {0 - p}");
  D("function {:inline} $ult.ref(p1:ref, p2:ref) returns (bool) {p1 < p2}");
  D("function {:inline} $ugt.ref(p1:ref, p2:ref) returns (bool) {p1 > p2}");
  D("function {:inline} $ule.ref(p1:ref, p2:ref) returns (bool) {p1 <= p2}");
  D("function {:inline} $uge.ref(p1:ref, p2:ref) returns (bool) {p1 >= p2}");
  D("function {:inline} $slt.ref(p1:ref, p2:ref) returns (bool) {p1 < p2}");
  D("function {:inline} $sgt.ref(p1:ref, p2:ref) returns (bool) {p1 > p2}");
  D("function {:inline} $sle.ref(p1:ref, p2:ref) returns (bool) {p1 <= p2}");
  D("function {:inline} $sge.ref(p1:ref, p2:ref) returns (bool) {p1 >= p2}");

  D("function {:inline} $isExternal(p: ref) returns (bool) { p < $GLOBALS_BOTTOM - 32768 }");
#endif

  // Memory debugging symbols
  D("type $mop;");
  D("procedure boogie_si_record_mop(m: $mop);");
  D("procedure boogie_si_record_bool(b: bool);");
  D("procedure boogie_si_record_i8(i: i8);");
  D("procedure boogie_si_record_i16(i: i16);");
  D("procedure boogie_si_record_i32(i: i32);");
  D("procedure boogie_si_record_i64(i: i64);");
  D("procedure boogie_si_record_ref(i: ref);");
  D("procedure boogie_si_record_float(f: float);");
  D("const $MOP: $mop;");

  D("const $GLOBALS_BOTTOM: ref;");

#if MEMORY_MODEL_NO_REUSE_IMPLS
  D("var $Alloc: [ref] bool;");
  D("var $CurrAddr:ref;");

  D("procedure $malloc(n: size) returns (p: ref)\n"
    "modifies $CurrAddr, $Alloc;\n"
    "{\n"
    "  assume $sgt.ref($CurrAddr, $NULL);\n"
    "  p := $CurrAddr;\n"
    "  if ($sgt.ref(n, $NULL)) {\n"
    "    $CurrAddr := $add.ref($CurrAddr, n);\n"
    "  } else {\n"
    "    $CurrAddr := $add.ref($CurrAddr, $REF_CONST_1);\n"
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
    "  assume $sgt.ref($CurrAddr, $NULL);\n"
    "  p := $CurrAddr;\n"
    "  if ($sgt.ref(n, $NULL)) {\n"
    "    $CurrAddr := $add.ref($CurrAddr, n);\n"
    "  } else {\n"
    "    $CurrAddr := $add.ref($CurrAddr, $REF_CONST_1);\n"
    "  }\n"
    "  $Alloc[p] := true;\n"
    "}");

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
  D("var $Alloc: [ref] bool;");
  D("var $Size: [ref] size;");
  D("var $CurrAddr:ref;");

  D("procedure $malloc(n: size) returns (p: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $sgt.ref(p, $NULL);\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: ref :: old($Alloc[q]) ==> ($slt.ref($add.ref(p, n), q) || $sgt.ref(p, $add.ref(q, $Size[q]))));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $sge.ref(n, $NULL) ==> (forall q: ref :: {$base(q)} $sle.ref(p, q) && $slt.ref(q, $add.ref(p, n)) ==> $base(q) == p);");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc;\n"
    "ensures !$Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));");

  D("procedure $alloca(n: size) returns (p: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $sgt.ref(p, $NULL);\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: ref :: old($Alloc[q]) ==> ($slt.ref($add.ref(p, n), q) || $sgt.ref(p, $add.ref(q, $Size[q]))));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $sge.ref(n, $NULL) ==> (forall q: ref :: {$base(q)} $sle.ref(p, q) && $slt.ref(q, $add.ref(p, n)) ==> $base(q) == p);");

#else // NO_REUSE does not reuse previously-allocated addresses
  D("var $Alloc: [ref] bool;");
  D("var $CurrAddr:ref;");
  D("procedure $malloc(n: size) returns (p: ref);\n"
    "modifies $CurrAddr, $Alloc;\n"
    "ensures $sgt.ref(p, $NULL);\n"
    "ensures p == old($CurrAddr);\n"
    "ensures $sgt.ref($CurrAddr, old($CurrAddr));\n"
    "ensures $sge.ref(n, $NULL) ==> $sge.ref($CurrAddr, $add.ref(old($CurrAddr), n));\n"
    "ensures $Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $sge.ref(n, $NULL) ==> (forall q: ref :: {$base(q)} $sle.ref(p, q) && $slt.ref(q, $add.ref(p, n)) ==> $base(q) == p);");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc;\n"
    "ensures !$Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));");

  D("procedure $alloca(n: size) returns (p: ref);\n"
    "modifies $CurrAddr, $Alloc;\n"
    "ensures $sgt.ref(p, $NULL);\n"
    "ensures p == old($CurrAddr);\n"
    "ensures $sgt.ref($CurrAddr, old($CurrAddr));\n"
    "ensures $sge.ref(n, $NULL) ==> $sge.ref($CurrAddr, $add.ref(old($CurrAddr), n));\n"
    "ensures $Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $sge.ref(n, $NULL) ==> (forall q: ref :: {$base(q)} $sle.ref(p, q) && $slt.ref(q, $add.ref(p, n)) ==> $base(q) == p);");
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
