//
// This file is distributed under the MIT License. See LICENSE for details.

#include <smack.h>
#include <stdlib.h>

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

void __VERIFIER_assume(int x) {
  __SMACK_dummy(x); __SMACK_code("assume @ != $0;", x);
}

#ifndef CUSTOM_VERIFIER_ASSERT
void __VERIFIER_assert(int x) {
  __SMACK_dummy(x); __SMACK_code("assert @ != $0;", x);
}
#endif

void __VERIFIER_error(void) {
  __SMACK_code("assert false;");
}

void exit(int x) {
  __SMACK_code("assume false;");
  while(1);
}

// Apparently used in SVCCOMP benchmarks
_Bool __VERIFIER_nondet_bool(void) {
  _Bool x = (_Bool)__VERIFIER_nondet_int();
  return x;
}

unsigned char __VERIFIER_nondet_uchar(void) {
  unsigned char x = __VERIFIER_nondet_unsigned_char();
  __VERIFIER_assume(x >= 0);
  return x;
}

unsigned short __VERIFIER_nondet_ushort(void) {
  unsigned short x = __VERIFIER_nondet_unsigned_short();
  __VERIFIER_assume(x >= 0);
  return x;
}

unsigned int __VERIFIER_nondet_uint(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  __VERIFIER_assume(x >= 0);
  return x;
 }

unsigned long __VERIFIER_nondet_ulong(void) {
  unsigned long x = __VERIFIER_nondet_unsigned_long();
  __VERIFIER_assume(x >= 0);
  return x;
}

void* __VERIFIER_nondet_pointer(void) {
  return __VERIFIER_nondet();
}

void* realloc(void* ptr, unsigned long size) {
  void* ret;
  if (ptr == 0 && size != 0) {
    ret = malloc(size);
  } else if (ptr != 0 && size == 0) {
    free(ptr);
    ret = ptr;
  } else if (ptr == 0 && size == 0) {
    ret = malloc(size); // Implementation defined
  }
  else {
    // Overapproximate the behavior of realloc
    ret = malloc(size);
    memcpy(ret, ptr, size);
  }
  return ret;
}

void* calloc(unsigned long num, unsigned long size) {
  void* ret;
  if (__VERIFIER_nondet_int()) {
    ret = 0;
  } else {
    ret = malloc(num * size);
    memset(ret, 0, num * size);
  }
  return ret;
}

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
  D(xstr(M(i128,args))); \
  D(xstr(M(i96,args))); \
  D(xstr(M(i64,args))); \
  D(xstr(M(i56,args))); \
  D(xstr(M(i48,args))); \
  D(xstr(M(i40,args))); \
  D(xstr(M(i32,args))); \
  D(xstr(M(i24,args))); \
  D(xstr(M(i16,args))); \
  D(xstr(M(i8,args))); \
  D(xstr(M(i1,args)));

#define DECLARE_EACH_BV_TYPE(M,args...) \
  D(xstr(M(bv128,args))); \
  D(xstr(M(bv96,args))); \
  D(xstr(M(bv64,args))); \
  D(xstr(M(bv56,args))); \
  D(xstr(M(bv48,args))); \
  D(xstr(M(bv40,args))); \
  D(xstr(M(bv32,args))); \
  D(xstr(M(bv24,args))); \
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

  DECLARE(INLINE_CONVERSION,bv128,bv96,$trunc,{i[96:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv64,$trunc,{i[64:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv56,$trunc,{i[56:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv48,$trunc,{i[48:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv40,$trunc,{i[40:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv32,$trunc,{i[32:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv24,$trunc,{i[24:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv64,$trunc,{i[64:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv56,$trunc,{i[56:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv48,$trunc,{i[48:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv40,$trunc,{i[40:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv32,$trunc,{i[32:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv24,$trunc,{i[24:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv56,$trunc,{i[56:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv48,$trunc,{i[48:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv40,$trunc,{i[40:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv32,$trunc,{i[32:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv24,$trunc,{i[24:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv64,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv56,bv48,$trunc,{i[48:0]});
  DECLARE(INLINE_CONVERSION,bv56,bv40,$trunc,{i[40:0]});
  DECLARE(INLINE_CONVERSION,bv56,bv32,$trunc,{i[32:0]});
  DECLARE(INLINE_CONVERSION,bv56,bv24,$trunc,{i[24:0]});
  DECLARE(INLINE_CONVERSION,bv56,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv56,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv56,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv48,bv32,$trunc,{i[32:0]});
  DECLARE(INLINE_CONVERSION,bv48,bv24,$trunc,{i[24:0]});
  DECLARE(INLINE_CONVERSION,bv48,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv48,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv48,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv40,bv32,$trunc,{i[32:0]});
  DECLARE(INLINE_CONVERSION,bv40,bv24,$trunc,{i[24:0]});
  DECLARE(INLINE_CONVERSION,bv40,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv40,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv40,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv32,bv24,$trunc,{i[24:0]});
  DECLARE(INLINE_CONVERSION,bv32,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv32,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv32,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv24,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv24,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv24,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv16,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv16,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv8,bv1,$trunc,{i[1:0]});

  DECLARE(INLINE_CONVERSION,bv1,bv8,$zext,{if i == 0bv1 then 0bv8 else 1bv8});
  DECLARE(INLINE_CONVERSION,bv1,bv16,$zext,{if i == 0bv1 then 0bv16 else 1bv16});
  DECLARE(INLINE_CONVERSION,bv1,bv24,$zext,{if i == 0bv1 then 0bv24 else 1bv24});
  DECLARE(INLINE_CONVERSION,bv1,bv32,$zext,{if i == 0bv1 then 0bv32 else 1bv32});
  DECLARE(INLINE_CONVERSION,bv1,bv40,$zext,{if i == 0bv1 then 0bv40 else 1bv40});
  DECLARE(INLINE_CONVERSION,bv1,bv48,$zext,{if i == 0bv1 then 0bv48 else 1bv48});
  DECLARE(INLINE_CONVERSION,bv1,bv56,$zext,{if i == 0bv1 then 0bv56 else 1bv56});
  DECLARE(INLINE_CONVERSION,bv1,bv64,$zext,{if i == 0bv1 then 0bv64 else 1bv64});
  DECLARE(INLINE_CONVERSION,bv1,bv96,$zext,{if i == 0bv1 then 0bv96 else 1bv96});
  DECLARE(INLINE_CONVERSION,bv1,bv128,$zext,{if i == 0bv1 then 0bv128 else 1bv128});
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv8.bv16(i: bv8) returns (bv16);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv8.bv24(i: bv8) returns (bv24);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv8.bv32(i: bv8) returns (bv32);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv8.bv40(i: bv8) returns (bv40);");
  D("function {:bvbuiltin \"(_ zero_extend 40)\"} $zext.bv8.bv48(i: bv8) returns (bv48);");
  D("function {:bvbuiltin \"(_ zero_extend 48)\"} $zext.bv8.bv56(i: bv8) returns (bv56);");
  D("function {:bvbuiltin \"(_ zero_extend 56)\"} $zext.bv8.bv64(i: bv8) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 88)\"} $zext.bv8.bv96(i: bv8) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 120)\"} $zext.bv8.bv128(i: bv8) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv16.bv24(i: bv16) returns (bv24);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv16.bv32(i: bv16) returns (bv32);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv16.bv40(i: bv16) returns (bv40);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv16.bv48(i: bv16) returns (bv48);");
  D("function {:bvbuiltin \"(_ zero_extend 40)\"} $zext.bv16.bv56(i: bv16) returns (bv56);");
  D("function {:bvbuiltin \"(_ zero_extend 48)\"} $zext.bv16.bv64(i: bv16) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 80)\"} $zext.bv16.bv96(i: bv16) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 112)\"} $zext.bv16.bv128(i: bv16) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv24.bv32(i: bv24) returns (bv32);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv24.bv40(i: bv24) returns (bv40);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv24.bv48(i: bv24) returns (bv48);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv24.bv56(i: bv24) returns (bv56);");
  D("function {:bvbuiltin \"(_ zero_extend 40)\"} $zext.bv24.bv64(i: bv24) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 72)\"} $zext.bv24.bv96(i: bv24) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 104)\"} $zext.bv24.bv128(i: bv24) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv32.bv40(i: bv32) returns (bv40);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv32.bv48(i: bv32) returns (bv48);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv32.bv56(i: bv32) returns (bv56);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv32.bv64(i: bv32) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 64)\"} $zext.bv32.bv96(i: bv32) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 96)\"} $zext.bv32.bv128(i: bv32) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv40.bv48(i: bv40) returns (bv48);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv40.bv56(i: bv40) returns (bv56);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv40.bv64(i: bv40) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 56)\"} $zext.bv40.bv96(i: bv40) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 88)\"} $zext.bv40.bv128(i: bv40) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv48.bv64(i: bv48) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 48)\"} $zext.bv48.bv96(i: bv48) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 80)\"} $zext.bv48.bv128(i: bv48) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv56.bv64(i: bv56) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 40)\"} $zext.bv56.bv96(i: bv56) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 72)\"} $zext.bv56.bv128(i: bv56) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv64.bv96(i: bv64) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 64)\"} $zext.bv64.bv128(i: bv64) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv96.bv128(i: bv96) returns (bv128);");

  DECLARE(INLINE_CONVERSION,bv1,bv8,$sext,{if i == 0bv1 then 0bv8 else 255bv8});
  DECLARE(INLINE_CONVERSION,bv1,bv16,$sext,{if i == 0bv1 then 0bv16 else 65535bv16});
  DECLARE(INLINE_CONVERSION,bv1,bv24,$sext,{if i == 0bv1 then 0bv24 else 16777215bv24});
  DECLARE(INLINE_CONVERSION,bv1,bv32,$sext,{if i == 0bv1 then 0bv32 else 4294967295bv32});
  DECLARE(INLINE_CONVERSION,bv1,bv40,$sext,{if i == 0bv1 then 0bv40 else 1099511627775bv40});
  DECLARE(INLINE_CONVERSION,bv1,bv48,$sext,{if i == 0bv1 then 0bv48 else 281474976710655bv48});
  DECLARE(INLINE_CONVERSION,bv1,bv56,$sext,{if i == 0bv1 then 0bv56 else 72057594037927935bv56});
  DECLARE(INLINE_CONVERSION,bv1,bv64,$sext,{if i == 0bv1 then 0bv64 else 18446744073709551615bv64});
  DECLARE(INLINE_CONVERSION,bv1,bv96,$sext,{if i == 0bv1 then 0bv96 else 79228162514264337593543950335bv96});
  DECLARE(INLINE_CONVERSION,bv1,bv128,$sext,{if i == 0bv1 then 0bv128 else 340282366920938463463374607431768211455bv128});
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv8.bv16(i: bv8) returns (bv16);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv8.bv24(i: bv8) returns (bv24);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv8.bv32(i: bv8) returns (bv32);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv8.bv40(i: bv8) returns (bv40);");
  D("function {:bvbuiltin \"(_ sign_extend 40)\"} $sext.bv8.bv48(i: bv8) returns (bv48);");
  D("function {:bvbuiltin \"(_ sign_extend 48)\"} $sext.bv8.bv56(i: bv8) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 56)\"} $sext.bv8.bv64(i: bv8) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 88)\"} $sext.bv8.bv96(i: bv8) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 120)\"} $sext.bv8.bv128(i: bv8) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv16.bv24(i: bv16) returns (bv24);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv16.bv32(i: bv16) returns (bv32);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv16.bv40(i: bv16) returns (bv40);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv16.bv48(i: bv16) returns (bv48);");
  D("function {:bvbuiltin \"(_ sign_extend 40)\"} $sext.bv16.bv56(i: bv16) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 48)\"} $sext.bv16.bv64(i: bv16) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 80)\"} $sext.bv16.bv96(i: bv16) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 112)\"} $sext.bv16.bv128(i: bv16) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv24.bv32(i: bv24) returns (bv32);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv24.bv40(i: bv24) returns (bv40);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv24.bv48(i: bv24) returns (bv48);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv24.bv56(i: bv24) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 40)\"} $sext.bv24.bv64(i: bv24) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 72)\"} $sext.bv24.bv96(i: bv24) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 104)\"} $sext.bv24.bv128(i: bv24) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv32.bv40(i: bv32) returns (bv40);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv32.bv48(i: bv32) returns (bv48);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv32.bv56(i: bv32) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv32.bv64(i: bv32) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 64)\"} $sext.bv32.bv96(i: bv32) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 96)\"} $sext.bv32.bv128(i: bv32) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv40.bv48(i: bv40) returns (bv48);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv40.bv56(i: bv40) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv40.bv64(i: bv40) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 56)\"} $sext.bv40.bv96(i: bv40) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 88)\"} $sext.bv40.bv128(i: bv40) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv48.bv56(i: bv48) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv48.bv64(i: bv48) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 48)\"} $sext.bv48.bv96(i: bv48) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 80)\"} $sext.bv48.bv128(i: bv48) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv56.bv64(i: bv56) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 40)\"} $sext.bv56.bv96(i: bv56) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 72)\"} $sext.bv56.bv128(i: bv56) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv64.bv96(i: bv64) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 64)\"} $sext.bv64.bv128(i: bv64) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv96.bv128(i: bv96) returns (bv128);");

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

  DECLARE(INLINE_CONVERSION,i128,i96,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i128,i64,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i128,i56,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i128,i48,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i128,i40,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i128,i32,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i128,i24,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i128,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i128,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i128,i1,$trunc,{i});

  DECLARE(INLINE_CONVERSION,i96,i64,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i56,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i48,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i40,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i32,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i24,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i1,$trunc,{i});

  DECLARE(INLINE_CONVERSION,i64,i56,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i64,i48,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i64,i40,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i64,i32,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i64,i24,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i64,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i64,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i64,i1,$trunc,{i});

  DECLARE(INLINE_CONVERSION,i56,i48,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i56,i40,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i56,i32,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i56,i24,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i56,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i56,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i56,i1,$trunc,{i});

  DECLARE(INLINE_CONVERSION,i48,i40,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i48,i32,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i48,i24,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i48,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i48,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i48,i1,$trunc,{i});

  DECLARE(INLINE_CONVERSION,i40,i32,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i40,i24,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i40,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i40,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i40,i1,$trunc,{i});

  DECLARE(INLINE_CONVERSION,i32,i24,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i32,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i32,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i32,i1,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i24,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i24,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i24,i1,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i16,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i16,i1,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i8,i1,$trunc,{i});

  DECLARE(INLINE_CONVERSION,i1,i8,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i16,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i24,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i32,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i40,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i16,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i24,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i32,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i40,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i24,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i32,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i40,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i32,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i40,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i40,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i48,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i48,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i48,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i48,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i56,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i56,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i56,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i64,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i64,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i96,i128,$zext,{i});

  DECLARE(INLINE_CONVERSION,i1,i8,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i16,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i24,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i40,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i16,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i24,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i40,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i24,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i40,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i40,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i40,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i48,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i48,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i48,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i48,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i56,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i56,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i56,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i64,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i64,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i96,i128,$sext,{i});

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

  D("function $fp2si.float.i128(f:float) returns (i128);");
  D("function $fp2ui.float.i128(f:float) returns (i128);");
  D("function $si2fp.i128.float(i:i128) returns (float);");
  D("function $ui2fp.i128.float(i:i128) returns (float);");
  D("function $fp2si.float.i96(f:float) returns (i96);");
  D("function $fp2ui.float.i96(f:float) returns (i96);");
  D("function $si2fp.i96.float(i:i96) returns (float);");
  D("function $ui2fp.i96.float(i:i96) returns (float);");
  D("function $fp2si.float.i64(f:float) returns (i64);");
  D("function $fp2ui.float.i64(f:float) returns (i64);");
  D("function $si2fp.i64.float(i:i64) returns (float);");
  D("function $ui2fp.i64.float(i:i64) returns (float);");
  D("function $fp2si.float.i56(f:float) returns (i56);");
  D("function $fp2ui.float.i56(f:float) returns (i56);");
  D("function $si2fp.i56.float(i:i56) returns (float);");
  D("function $ui2fp.i56.float(i:i56) returns (float);");
  D("function $fp2si.float.i48(f:float) returns (i48);");
  D("function $fp2ui.float.i48(f:float) returns (i48);");
  D("function $si2fp.i48.float(i:i48) returns (float);");
  D("function $ui2fp.i48.float(i:i48) returns (float);");
  D("function $fp2si.float.i40(f:float) returns (i40);");
  D("function $fp2ui.float.i40(f:float) returns (i40);");
  D("function $si2fp.i40.float(i:i40) returns (float);");
  D("function $ui2fp.i40.float(i:i40) returns (float);");

  D("function $fp2si.float.i32(f:float) returns (i32);");
  D("function $fp2ui.float.i32(f:float) returns (i32);");
  D("function $si2fp.i32.float(i:i32) returns (float);");
  D("function $ui2fp.i32.float(i:i32) returns (float);");
  D("function $fp2si.float.i24(f:float) returns (i24);");
  D("function $fp2ui.float.i24(f:float) returns (i24);");
  D("function $si2fp.i24.float(i:i24) returns (float);");
  D("function $ui2fp.i24.float(i:i24) returns (float);");
  D("function $fp2si.float.i16(f:float) returns (i16);");
  D("function $fp2ui.float.i16(f:float) returns (i16);");
  D("function $si2fp.i16.float(i:i16) returns (float);");
  D("function $ui2fp.i16.float(i:i16) returns (float);");
  D("function $fp2si.float.i8(f:float) returns (i8);");
  D("function $fp2ui.float.i8(f:float) returns (i8);");
  D("function $si2fp.i8.float(i:i8) returns (float);");
  D("function $ui2fp.i8.float(i:i8) returns (float);");

  D("function $fptrunc.float.float(f:float) returns (float);");
  D("function $fpext.float.float(f:float) returns (float);");
  D("function $fp2si.float.bv128(f:float) returns (bv128);");
  D("function $fp2ui.float.bv128(f:float) returns (bv128);");
  D("function $si2fp.bv128.float(i:bv128) returns (float);");
  D("function $ui2fp.bv128.float(i:bv128) returns (float);");
  D("function $fp2si.float.bv96(f:float) returns (bv96);");
  D("function $fp2ui.float.bv96(f:float) returns (bv96);");
  D("function $si2fp.bv96.float(i:bv96) returns (float);");
  D("function $ui2fp.bv96.float(i:bv96) returns (float);");
  D("function $fp2si.float.bv64(f:float) returns (bv64);");
  D("function $fp2ui.float.bv64(f:float) returns (bv64);");
  D("function $si2fp.bv64.float(i:bv64) returns (float);");
  D("function $ui2fp.bv64.float(i:bv64) returns (float);");
  D("function $fp2si.float.bv56(f:float) returns (bv56);");
  D("function $fp2ui.float.bv56(f:float) returns (bv56);");
  D("function $si2fp.bv56.float(i:bv56) returns (float);");
  D("function $ui2fp.bv56.float(i:bv56) returns (float);");
  D("function $fp2si.float.bv48(f:float) returns (bv48);");
  D("function $fp2ui.float.bv48(f:float) returns (bv48);");
  D("function $si2fp.bv48.float(i:bv48) returns (float);");
  D("function $ui2fp.bv48.float(i:bv48) returns (float);");
  D("function $fp2si.float.bv40(f:float) returns (bv40);");
  D("function $fp2ui.float.bv40(f:float) returns (bv40);");
  D("function $si2fp.bv40.float(i:bv40) returns (float);");
  D("function $ui2fp.bv40.float(i:bv40) returns (float);");
  D("function $fp2si.float.bv32(f:float) returns (bv32);");
  D("function $fp2ui.float.bv32(f:float) returns (bv32);");
  D("function $si2fp.bv32.float(i:bv32) returns (float);");
  D("function $ui2fp.bv32.float(i:bv32) returns (float);");
  D("function $fp2si.float.bv24(f:float) returns (bv24);");
  D("function $fp2ui.float.bv24(f:float) returns (bv24);");
  D("function $si2fp.bv24.float(i:bv24) returns (float);");
  D("function $ui2fp.bv24.float(i:bv24) returns (float);");
  D("function $fp2si.float.bv16(f:float) returns (bv16);");
  D("function $fp2ui.float.bv16(f:float) returns (bv16);");
  D("function $si2fp.bv16.float(i:bv16) returns (float);");
  D("function $ui2fp.bv16.float(i:bv16) returns (float);");
  D("function $fp2si.float.bv8(f:float) returns (bv8);");
  D("function $fp2ui.float.bv8(f:float) returns (bv8);");
  D("function $si2fp.bv8.float(i:bv8) returns (float);");
  D("function $ui2fp.bv8.float(i:bv8) returns (float);");

#ifndef NO_FORALL
  D("axiom (forall f1, f2: float :: f1 != f2 || $foeq.bool(f1,f2));");

  D("axiom (forall i: i128 :: $fp2ui.float.i128($ui2fp.i128.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i128.float($fp2ui.float.i128(f)) == f);");
  D("axiom (forall i: i128 :: $fp2si.float.i128($si2fp.i128.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i128.float($fp2si.float.i128(f)) == f);");
  D("axiom (forall i: i96 :: $fp2ui.float.i96($ui2fp.i96.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i96.float($fp2ui.float.i96(f)) == f);");
  D("axiom (forall i: i96 :: $fp2si.float.i96($si2fp.i96.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i96.float($fp2si.float.i96(f)) == f);");
  D("axiom (forall i: i64 :: $fp2ui.float.i64($ui2fp.i64.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i64.float($fp2ui.float.i64(f)) == f);");
  D("axiom (forall i: i64 :: $fp2si.float.i64($si2fp.i64.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i64.float($fp2si.float.i64(f)) == f);");
  D("axiom (forall i: i56 :: $fp2ui.float.i56($ui2fp.i56.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i56.float($fp2ui.float.i56(f)) == f);");
  D("axiom (forall i: i56 :: $fp2si.float.i56($si2fp.i56.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i56.float($fp2si.float.i56(f)) == f);");
  D("axiom (forall i: i48 :: $fp2ui.float.i48($ui2fp.i48.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i48.float($fp2ui.float.i48(f)) == f);");
  D("axiom (forall i: i48 :: $fp2si.float.i48($si2fp.i48.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i48.float($fp2si.float.i48(f)) == f);");
  D("axiom (forall i: i40 :: $fp2ui.float.i40($ui2fp.i40.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i40.float($fp2ui.float.i40(f)) == f);");
  D("axiom (forall i: i40 :: $fp2si.float.i40($si2fp.i40.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i40.float($fp2si.float.i40(f)) == f);");
  D("axiom (forall i: i32 :: $fp2ui.float.i32($ui2fp.i32.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i32.float($fp2ui.float.i32(f)) == f);");
  D("axiom (forall i: i32 :: $fp2si.float.i32($si2fp.i32.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i32.float($fp2si.float.i32(f)) == f);");
  D("axiom (forall i: i24 :: $fp2ui.float.i24($ui2fp.i24.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i24.float($fp2ui.float.i24(f)) == f);");
  D("axiom (forall i: i24 :: $fp2si.float.i24($si2fp.i24.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i24.float($fp2si.float.i24(f)) == f);");
  D("axiom (forall i: i16 :: $fp2ui.float.i16($ui2fp.i16.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i16.float($fp2ui.float.i16(f)) == f);");
  D("axiom (forall i: i16 :: $fp2si.float.i16($si2fp.i16.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i16.float($fp2si.float.i16(f)) == f);");
  D("axiom (forall i: i8 :: $fp2ui.float.i8($ui2fp.i8.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i8.float($fp2ui.float.i8(f)) == f);");
  D("axiom (forall i: i8 :: $fp2si.float.i8($si2fp.i8.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i8.float($fp2si.float.i8(f)) == f);");
#endif

  // Memory Model
  D("const $GLOBALS_BOTTOM: ref;");
  D("const $EXTERNS_BOTTOM: ref;");
  D("const $MALLOC_TOP: ref;");
  D("function $base(ref) returns (ref);");
  D("function {:inline} $isExternal(p: ref) returns (bool) {$slt.ref.bool(p,$EXTERNS_BOTTOM)}");

  D("function {:inline} $load.i128(M: [ref] i128, p: ref) returns (i128) { M[p] }");
  D("function {:inline} $load.i96(M: [ref] i96, p: ref) returns (i96) { M[p] }");
  D("function {:inline} $load.i64(M: [ref] i64, p: ref) returns (i64) { M[p] }");
  D("function {:inline} $load.i56(M: [ref] i56, p: ref) returns (i56) { M[p] }");
  D("function {:inline} $load.i48(M: [ref] i48, p: ref) returns (i48) { M[p] }");
  D("function {:inline} $load.i40(M: [ref] i40, p: ref) returns (i40) { M[p] }");
  D("function {:inline} $load.i32(M: [ref] i32, p: ref) returns (i32) { M[p] }");
  D("function {:inline} $load.i24(M: [ref] i24, p: ref) returns (i24) { M[p] }");
  D("function {:inline} $load.i16(M: [ref] i16, p: ref) returns (i16) { M[p] }");
  D("function {:inline} $load.i8(M: [ref] i8, p: ref) returns (i8) { M[p] }");
  D("function {:inline} $load.i1(M: [ref] i1, p: ref) returns (i1) { M[p] }");

  D("function {:inline} $load.bv128(M: [ref] bv128, p: ref) returns (bv128) { M[p] }");
  D("function {:inline} $load.bv96(M: [ref] bv96, p: ref) returns (bv96) { M[p] }");
  D("function {:inline} $load.bv64(M: [ref] bv64, p: ref) returns (bv64) { M[p] }");
  D("function {:inline} $load.bv56(M: [ref] bv56, p: ref) returns (bv56) { M[p] }");
  D("function {:inline} $load.bv48(M: [ref] bv48, p: ref) returns (bv48) { M[p] }");
  D("function {:inline} $load.bv40(M: [ref] bv40, p: ref) returns (bv40) { M[p] }");
  D("function {:inline} $load.bv32(M: [ref] bv32, p: ref) returns (bv32) { M[p] }");
  D("function {:inline} $load.bv24(M: [ref] bv24, p: ref) returns (bv24) { M[p] }");
  D("function {:inline} $load.bv16(M: [ref] bv16, p: ref) returns (bv16) { M[p] }");
  D("function {:inline} $load.bv8(M: [ref] bv8, p: ref) returns (bv8) { M[p] }");
  D("function {:inline} $load.bv1(M: [ref] bv8, p: ref) returns (bv8) { M[p] }");

  D("function {:inline} $load.bytes.bv128(M: [ref] bv8, p: ref) returns (bv128)"
    "{ $load.bytes.bv64(M, $add.ref(p, $8.ref)) ++ $load.bytes.bv64(M, p) }");
  D("function {:inline} $load.bytes.bv96(M: [ref] bv8, p: ref) returns (bv96)"
    "{ $load.bytes.bv64(M, $add.ref(p, $4.ref)) ++ $load.bytes.bv32(M, p) }");
  D("function {:inline} $load.bytes.bv64(M: [ref] bv8, p: ref) returns (bv64)"
    "{ $load.bytes.bv32(M, $add.ref(p, $4.ref)) ++ $load.bytes.bv32(M, p) }");
  D("function {:inline} $load.bytes.bv56(M: [ref] bv8, p: ref) returns (bv56)"
    "{ $load.bytes.bv24(M, $add.ref(p, $4.ref)) ++ $load.bytes.bv32(M, p) }");
  D("function {:inline} $load.bytes.bv48(M: [ref] bv8, p: ref) returns (bv48)"
    "{ $load.bytes.bv16(M, $add.ref(p, $4.ref)) ++ $load.bytes.bv32(M, p) }");
  D("function {:inline} $load.bytes.bv40(M: [ref] bv8, p: ref) returns (bv40)"
    "{ M[$add.ref(p, $4.ref)] ++ $load.bytes.bv32(M, p) }");
  D("function {:inline} $load.bytes.bv32(M: [ref] bv8, p: ref) returns (bv32)"
    "{ M[$add.ref(p, $3.ref)] ++ M[$add.ref(p, $2.ref)] ++ M[$add.ref(p, $1.ref)]++M[p] }");
  D("function {:inline} $load.bytes.bv24(M: [ref] bv8, p: ref) returns (bv24)"
    "{ M[$add.ref(p, $2.ref)] ++ M[$add.ref(p, $1.ref)]++M[p] }");
  D("function {:inline} $load.bytes.bv16(M: [ref] bv8, p: ref) returns (bv16)"
    "{ M[$add.ref(p, $1.ref)] ++ M[p] }");
  D("function {:inline} $load.bytes.bv8(M: [ref] bv8, p: ref) returns (bv8) { M[p] }");

  D("function {:inline} $store.i128(M: [ref] i128, p: ref, v: i128) returns ([ref] i128) { M[p := v] }");
  D("function {:inline} $store.i96(M: [ref] i96, p: ref, v: i96) returns ([ref] i96) { M[p := v] }");
  D("function {:inline} $store.i64(M: [ref] i64, p: ref, v: i64) returns ([ref] i64) { M[p := v] }");
  D("function {:inline} $store.i56(M: [ref] i56, p: ref, v: i56) returns ([ref] i56) { M[p := v] }");
  D("function {:inline} $store.i48(M: [ref] i48, p: ref, v: i48) returns ([ref] i48) { M[p := v] }");
  D("function {:inline} $store.i40(M: [ref] i40, p: ref, v: i40) returns ([ref] i40) { M[p := v] }");
  D("function {:inline} $store.i32(M: [ref] i32, p: ref, v: i32) returns ([ref] i32) { M[p := v] }");
  D("function {:inline} $store.i24(M: [ref] i24, p: ref, v: i24) returns ([ref] i24) { M[p := v] }");
  D("function {:inline} $store.i16(M: [ref] i16, p: ref, v: i16) returns ([ref] i16) { M[p := v] }");
  D("function {:inline} $store.i8(M: [ref] i8, p: ref, v: i8) returns ([ref] i8) { M[p := v] }");
  D("function {:inline} $store.i1(M: [ref] i1, p: ref, v: i1) returns ([ref] i1) { M[p := v] }");

  D("function {:inline} $store.bv128(M: [ref] bv128, p: ref, v: bv128) returns ([ref] bv128) { M[p := v] }");
  D("function {:inline} $store.bv96(M: [ref] bv96, p: ref, v: bv96) returns ([ref] bv96) { M[p := v] }");
  D("function {:inline} $store.bv64(M: [ref] bv64, p: ref, v: bv64) returns ([ref] bv64) { M[p := v] }");
  D("function {:inline} $store.bv56(M: [ref] bv56, p: ref, v: bv56) returns ([ref] bv56) { M[p := v] }");
  D("function {:inline} $store.bv48(M: [ref] bv48, p: ref, v: bv48) returns ([ref] bv48) { M[p := v] }");
  D("function {:inline} $store.bv40(M: [ref] bv40, p: ref, v: bv40) returns ([ref] bv40) { M[p := v] }");
  D("function {:inline} $store.bv32(M: [ref] bv32, p: ref, v: bv32) returns ([ref] bv32) { M[p := v] }");
  D("function {:inline} $store.bv24(M: [ref] bv24, p: ref, v: bv24) returns ([ref] bv24) { M[p := v] }");
  D("function {:inline} $store.bv16(M: [ref] bv16, p: ref, v: bv16) returns ([ref] bv16) { M[p := v] }");
  D("function {:inline} $store.bv8(M: [ref] bv8, p: ref, v: bv8) returns ([ref] bv8) { M[p := v] }");
  D("function {:inline} $store.bv1(M: [ref] bv8, p: ref, v: bv8) returns ([ref] bv8) { M[p := v] }");

  D("function {:inline} $store.bytes.bv128(M:[ref]bv8, p:ref, v:bv128) returns ([ref]bv8){"
    "M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]"
    "[$add.ref(p, $2.ref) := v[24:16]][$add.ref(p, $3.ref) := v[32:24]]"
    "[$add.ref(p, $4.ref) := v[40:32]][$add.ref(p, $5.ref) := v[48:40]]"
    "[$add.ref(p, $6.ref) := v[56:48]][$add.ref(p, $7.ref) := v[64:56]]"
    "[$add.ref(p, $7.ref) := v[72:64]][$add.ref(p, $8.ref) := v[80:72]]"
    "[$add.ref(p, $9.ref) := v[88:80]][$add.ref(p, $10.ref) := v[96:88]]"
    "[$add.ref(p, $11.ref) := v[104:96]][$add.ref(p, $12.ref) := v[112:104]]"
    "[$add.ref(p, $13.ref) := v[120:112]][$add.ref(p, $14.ref) := v[128:120]]}");
  D("function {:inline} $store.bytes.bv96(M:[ref]bv8, p:ref, v:bv96) returns ([ref]bv8){"
    "M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]"
    "[$add.ref(p, $2.ref) := v[24:16]][$add.ref(p, $3.ref) := v[32:24]]"
    "[$add.ref(p, $4.ref) := v[40:32]][$add.ref(p, $5.ref) := v[48:40]]"
    "[$add.ref(p, $6.ref) := v[56:48]][$add.ref(p, $7.ref) := v[64:56]]"
    "[$add.ref(p, $7.ref) := v[72:64]][$add.ref(p, $8.ref) := v[80:72]]"
    "[$add.ref(p, $9.ref) := v[88:80]][$add.ref(p, $10.ref) := v[96:88]]}");
  D("function {:inline} $store.bytes.bv64(M:[ref]bv8, p:ref, v:bv64) returns ([ref]bv8){"
    "M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]"
    "[$add.ref(p, $2.ref) := v[24:16]][$add.ref(p, $3.ref) := v[32:24]]"
    "[$add.ref(p, $4.ref) := v[40:32]][$add.ref(p, $5.ref) := v[48:40]]"
    "[$add.ref(p, $6.ref) := v[56:48]][$add.ref(p, $7.ref) := v[64:56]]}");
  D("function {:inline} $store.bytes.bv56(M:[ref]bv8, p:ref, v:bv56) returns ([ref]bv8){"
    "M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]"
    "[$add.ref(p, $2.ref) := v[24:16]][$add.ref(p, $3.ref) := v[32:24]]"
    "[$add.ref(p, $4.ref) := v[40:32]][$add.ref(p, $5.ref) := v[48:40]]"
    "[$add.ref(p, $6.ref) := v[56:48]]}");
  D("function {:inline} $store.bytes.bv48(M:[ref]bv8, p:ref, v:bv48) returns ([ref]bv8){"
    "M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]"
    "[$add.ref(p, $2.ref) := v[24:16]][$add.ref(p, $3.ref) := v[32:24]]"
    "[$add.ref(p, $4.ref) := v[40:32]][$add.ref(p, $5.ref) := v[48:40]]}");
  D("function {:inline} $store.bytes.bv40(M:[ref]bv8, p:ref, v:bv40) returns ([ref]bv8){"
    "M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]"
    "[$add.ref(p, $2.ref) := v[24:16]][$add.ref(p, $3.ref) := v[32:24]]"
    "[$add.ref(p, $4.ref) := v[40:32]]}");
  D("function {:inline} $store.bytes.bv32(M:[ref]bv8, p:ref, v:bv32) returns ([ref]bv8) {"
    "M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]"
    "[$add.ref(p, $2.ref) := v[24:16]][$add.ref(p, $3.ref) := v[32:24]]}");
  D("function {:inline} $store.bytes.bv24(M:[ref]bv8, p:ref, v:bv24) returns ([ref]bv8) {"
    "M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]"
    "[$add.ref(p, $2.ref) := v[24:16]]}");
  D("function {:inline} $store.bytes.bv16(M:[ref]bv8, p:ref, v:bv16) returns ([ref]bv8) {"
    "M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]}");
  D("function {:inline} $store.bytes.bv8(M:[ref]bv8, p:ref, v:bv8) returns ([ref]bv8) {M[p := v]}");

  D("function {:inline} $load.ref(M: [ref] ref, p: ref) returns (ref) { M[p] }");
  D("function {:inline} $store.ref(M: [ref] ref, p: ref, v: ref) returns ([ref] ref) { M[p := v] }");

  D("function {:inline} $load.float(M: [ref] float, p: ref) returns (float) { M[p] }");
  D("function {:inline} $store.float(M: [ref] float, p: ref, v: float) returns ([ref] float) { M[p := v] }");


  // Memory debugging symbols
  D("type $mop;");
  D("procedure boogie_si_record_mop(m: $mop);");
  D("const $MOP: $mop;");

  DECLARE(RECORD_PROC, bool);
  DECLARE(RECORD_PROC, i1);
  DECLARE(RECORD_PROC, i8);
  DECLARE(RECORD_PROC, i16);
  DECLARE(RECORD_PROC, i24);
  DECLARE(RECORD_PROC, i32);
  DECLARE(RECORD_PROC, i40);
  DECLARE(RECORD_PROC, i48);
  DECLARE(RECORD_PROC, i56);
  DECLARE(RECORD_PROC, i64);
  DECLARE(RECORD_PROC, i96);
  DECLARE(RECORD_PROC, i128);
  DECLARE(RECORD_PROC, bv1);
  DECLARE(RECORD_PROC, bv8);
  DECLARE(RECORD_PROC, bv16);
  DECLARE(RECORD_PROC, bv24);
  DECLARE(RECORD_PROC, bv32);
  DECLARE(RECORD_PROC, bv40);
  DECLARE(RECORD_PROC, bv48);
  DECLARE(RECORD_PROC, bv56);
  DECLARE(RECORD_PROC, bv64);
  DECLARE(RECORD_PROC, bv96);
  DECLARE(RECORD_PROC, bv128);
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

void __SMACK_init_func_memory_model(void) {
  __SMACK_code("$CurrAddr := $1024.ref;");
}
