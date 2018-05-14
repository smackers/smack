//
// This file is distributed under the MIT License. See LICENSE for details.

#include <smack.h>
#include <limits.h>
#include <stddef.h>
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
#if !MEMORY_SAFETY && !SIGNED_INTEGER_OVERFLOW_CHECK
  __SMACK_dummy(x); __SMACK_code("assert @ != $0;", x);
#endif
}
#endif

void __VERIFIER_error(void) {
#if !MEMORY_SAFETY && !SIGNED_INTEGER_OVERFLOW_CHECK
  __SMACK_code("assert false;");
#else
  __SMACK_code("assume false;");
#endif
}

void __SMACK_check_overflow(int flag) {
  __SMACK_dummy(flag); __SMACK_code("assert {:overflow} @ == $0;", flag);
}

void exit(int x) {
#if MEMORY_SAFETY
  __SMACK_code("assert $allocatedCounter == 0;");
#endif
  __SMACK_code("assume false;");
  while(1);
}

char __VERIFIER_nondet_char(void) {
  char x = __SMACK_nondet_char();
  __VERIFIER_assume(x >= SCHAR_MIN && x <= SCHAR_MAX);
  return x;
}

signed char __VERIFIER_nondet_signed_char(void) {
  signed char x = __SMACK_nondet_signed_char();
  __VERIFIER_assume(x >= SCHAR_MIN && x <= SCHAR_MAX);
  return x;
}

unsigned char __VERIFIER_nondet_unsigned_char(void) {
  unsigned char x = __SMACK_nondet_unsigned_char();
  __VERIFIER_assume(x >= 0 && x <= UCHAR_MAX);
  return x;
}

short __VERIFIER_nondet_short(void) {
  short x = __SMACK_nondet_short();
  __VERIFIER_assume(x >= SHRT_MIN && x <= SHRT_MAX);
  return x;
}

signed short __VERIFIER_nondet_signed_short(void) {
  signed short x = __SMACK_nondet_signed_short();
  __VERIFIER_assume(x >= SHRT_MIN && x <= SHRT_MAX);
  return x;
}

signed short int __VERIFIER_nondet_signed_short_int(void) {
  signed short int x = __SMACK_nondet_signed_short_int();
  __VERIFIER_assume(x >= SHRT_MIN && x <= SHRT_MAX);
  return x;
}

unsigned short __VERIFIER_nondet_unsigned_short(void) {
  unsigned short x = __SMACK_nondet_unsigned_short();
  __VERIFIER_assume(x >= 0 && x <= USHRT_MAX);
  return x;
}

unsigned short int __VERIFIER_nondet_unsigned_short_int(void) {
  unsigned short int x = __SMACK_nondet_unsigned_short_int();
  __VERIFIER_assume(x >= 0 && x <= USHRT_MAX);
  return x;
}

int __VERIFIER_nondet_int(void) {
  int x = __SMACK_nondet_int();
  __VERIFIER_assume(x >= INT_MIN && x <= INT_MAX);
  return x;
}

signed int __VERIFIER_nondet_signed_int(void) {
  signed int x = __SMACK_nondet_signed_int();
  __VERIFIER_assume(x >= INT_MIN && x <= INT_MAX);
  return x;
}

unsigned __VERIFIER_nondet_unsigned(void) {
  unsigned x = __SMACK_nondet_unsigned();
  __VERIFIER_assume(x >= 0 && x <= UINT_MAX);
  return x;
}

unsigned int __VERIFIER_nondet_unsigned_int(void) {
  unsigned int x = __SMACK_nondet_unsigned_int();
  __VERIFIER_assume(x >= 0 && x <= UINT_MAX);
  return x;
}

long __VERIFIER_nondet_long(void) {
  long x = __SMACK_nondet_long();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

long int __VERIFIER_nondet_long_int(void) {
  long int x = __SMACK_nondet_long_int();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

signed long __VERIFIER_nondet_signed_long(void) {
  signed long x = __SMACK_nondet_signed_long();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

signed long int __VERIFIER_nondet_signed_long_int(void) {
  signed long int x = __SMACK_nondet_signed_long_int();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

unsigned long __VERIFIER_nondet_unsigned_long(void) {
  unsigned long x = __SMACK_nondet_unsigned_long();
  __VERIFIER_assume(x >= 0 && x <= ULONG_MAX);
  return x;
}

unsigned long int __VERIFIER_nondet_unsigned_long_int(void) {
  unsigned long int x = __SMACK_nondet_unsigned_long_int();
  __VERIFIER_assume(x >= 0 && x <= ULONG_MAX);
  return x;
}

long long __VERIFIER_nondet_long_long(void) {
  long long x = __SMACK_nondet_long_long();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

long long int __VERIFIER_nondet_long_long_int(void) {
  long long int x = __SMACK_nondet_long_long_int();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

signed long long __VERIFIER_nondet_signed_long_long(void) {
  signed long long x = __SMACK_nondet_signed_long_long();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

signed long long int __VERIFIER_nondet_signed_long_long_int(void) {
  signed long long int x = __SMACK_nondet_signed_long_long_int();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

unsigned long long __VERIFIER_nondet_unsigned_long_long(void) {
  unsigned long long x = __SMACK_nondet_unsigned_long_long();
  __VERIFIER_assume(x >= 0 && x <= ULLONG_MAX);
  return x;
}

unsigned long long int __VERIFIER_nondet_unsigned_long_long_int(void) {
  unsigned long long int x = __SMACK_nondet_unsigned_long_long_int();
  __VERIFIER_assume(x >= 0 && x <= ULLONG_MAX);
  return x;
}

// Used in SVCCOMP benchmarks

#ifdef __cplusplus
bool __VERIFIER_nondet_bool(void) {
  bool x = (bool)__VERIFIER_nondet_int();
  __VERIFIER_assume(x == 0 || x == 1);
  return x;
}
#else
_Bool __VERIFIER_nondet_bool(void) {
  _Bool x = (_Bool)__VERIFIER_nondet_int();
  __VERIFIER_assume(x == 0 || x == 1);
  return x;
}
#endif

unsigned char __VERIFIER_nondet_uchar(void) {
  unsigned char x = __VERIFIER_nondet_unsigned_char();
  return x;
}

unsigned short __VERIFIER_nondet_ushort(void) {
  unsigned short x = __VERIFIER_nondet_unsigned_short();
  return x;
}

unsigned int __VERIFIER_nondet_uint(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  return x;
 }

unsigned long __VERIFIER_nondet_ulong(void) {
  unsigned long x = __VERIFIER_nondet_unsigned_long();
  return x;
}

void* __VERIFIER_nondet_pointer(void) {
  return __VERIFIER_nondet();
}

void* calloc(size_t num, size_t size) {
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

#define UNINTERPRETED_UNARY_OP(type,name) \
  function name.type(i: type) returns (type);

#define UNINTERPRETED_BINARY_OP(type,name) \
  function name.type(i1: type, i2: type) returns (type);

#define UNINTERPRETED_UNARY_PRED(type,name) \
  function name.type(i: type) returns (i1);

#define UNINTERPRETED_BINARY_PRED(type,name) \
  function name.type(i1: type, i2: type) returns (i1);

#define UNINTERPRETED_BINARY_COMP(type,name) \
  function name.type.bool(i1: type, i2: type) returns (bool);

#define UNINTERPRETED_CONVERSION(t1,t2,name) \
  function name.t1.t2(i: t1) returns (t2);

#define UNARY_OP(attrib,type,name,body) \
  function {:attrib} name.type(i: type) returns (type) body

#define BINARY_OP(attrib,type,name,body) \
  function {:attrib} name.type(i1: type, i2: type) returns (type) body

#define BINARY_COMP(attrib,type,name,cond) \
  function {:attrib} name.type.bool(i1: type, i2: type) returns (bool) cond

#define INLINE_BINARY_OP(type,name,cond) \
  BINARY_OP(inline,type,name,cond)

#define INLINE_BINARY_COMP(type,name,cond) \
  BINARY_COMP(inline,type,name,cond)

#define INLINE_BINARY_PRED(type,name,cond) \
  INLINE_BINARY_COMP(type,name,cond) \
  function {:inline} name.type(i1: type, i2: type) returns (i1) {if name.type.bool(i1,i2) then 1 else 0}

#define INLINE_BINARY_BV_PRED(type,name,cond) \
  INLINE_BINARY_COMP(type,name,cond) \
  function {:inline} name.type(i1: type, i2: type) returns (bv1) {if name.type.bool(i1,i2) then 1bv1 else 0bv1}

#define BUILTIN_CONVERSION(t1,t2,name,prim) \
  function {:builtin xstr(prim)} name.t1.t2(i: t1) returns (t2);

#define INLINE_CONVERSION(t1,t2,name,body) \
  function {:inline} name.t1.t2(i: t1) returns (t2) body

#define BUILTIN_UNARY_OP(type,name,prim) \
  UNARY_OP(builtin xstr(prim),type,name,);

#define BUILTIN_UNARY_PRED(type,name,prim) \
  function {:builtin xstr(prim)} name.type.bool(i: type) returns (bool);

#define BUILTIN_BINARY_COMP(type,name,prim) \
  BINARY_COMP(builtin xstr(prim),type,name,);

#define BUILTIN_BINARY_OP(type,name,prim) \
  BINARY_OP(builtin xstr(prim),type,name,);

#define BVBUILTIN_UNARY_OP(type,name,prim) \
  UNARY_OP(bvbuiltin xstr(prim),type,name,);

#define BVBUILTIN_BINARY_OP(type,name,prim) \
  BINARY_OP(bvbuiltin xstr(prim),type,name,);

#define INLINE_BVBUILTIN_BINARY_PRED(type,name,prim) \
  BINARY_COMP(bvbuiltin xstr(prim),type,name,); \
  function {:inline} name.type(i1: type, i2: type) returns (bv1) {if name.type.bool(i1,i2) then 1bv1 else 0bv1}

#define INLINE_BVBUILTIN_BINARY_SELECT(type,name,pred) \
  function {:inline} name.type(i1: type, i2: type) returns (type) {if pred.type.bool(i1,i2) then i1 else i2}


#define D(d) __SMACK_top_decl(d)

#define DECLARE(M,args...) \
  D(xstr(M(args)))

#include "smack-macros.h"

#define DECLARE_EACH_FLOAT_TYPE(M,args...) \
  D(xstr(M(bvhalf,args))); \
  D(xstr(M(bvfloat,args))); \
  D(xstr(M(bvdouble,args))); \
  D(xstr(M(bvlongdouble,args)));

void __SMACK_decls(void) {

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

  DECLARE_EACH_BV_TYPE(INLINE_BINARY_BV_PRED, $eq, {i1 == i2})
  DECLARE_EACH_BV_TYPE(INLINE_BINARY_BV_PRED, $ne, {i1 != i2})
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $ule, bvule)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $ult, bvult)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $uge, bvuge)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $ugt, bvugt)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $sle, bvsle)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $slt, bvslt)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $sge, bvsge)
  DECLARE_EACH_BV_TYPE(INLINE_BVBUILTIN_BINARY_PRED, $sgt, bvsgt)

  DECLARE_BV_TRUNCS

  DECLARE(INLINE_CONVERSION,bv1,bv8,$zext,{if i == 0bv1 then 0bv8 else 1bv8});
  DECLARE(INLINE_CONVERSION,bv1,bv16,$zext,{if i == 0bv1 then 0bv16 else 1bv16});
  DECLARE(INLINE_CONVERSION,bv1,bv24,$zext,{if i == 0bv1 then 0bv24 else 1bv24});
  DECLARE(INLINE_CONVERSION,bv1,bv32,$zext,{if i == 0bv1 then 0bv32 else 1bv32});
  DECLARE(INLINE_CONVERSION,bv1,bv40,$zext,{if i == 0bv1 then 0bv40 else 1bv40});
  DECLARE(INLINE_CONVERSION,bv1,bv48,$zext,{if i == 0bv1 then 0bv48 else 1bv48});
  DECLARE(INLINE_CONVERSION,bv1,bv56,$zext,{if i == 0bv1 then 0bv56 else 1bv56});
  DECLARE(INLINE_CONVERSION,bv1,bv64,$zext,{if i == 0bv1 then 0bv64 else 1bv64});
  DECLARE(INLINE_CONVERSION,bv1,bv88,$zext,{if i == 0bv1 then 0bv88 else 1bv88});
  DECLARE(INLINE_CONVERSION,bv1,bv96,$zext,{if i == 0bv1 then 0bv96 else 1bv96});
  DECLARE(INLINE_CONVERSION,bv1,bv128,$zext,{if i == 0bv1 then 0bv128 else 1bv128});
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv8.bv16(i: bv8) returns (bv16);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv8.bv24(i: bv8) returns (bv24);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv8.bv32(i: bv8) returns (bv32);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv8.bv40(i: bv8) returns (bv40);");
  D("function {:bvbuiltin \"(_ zero_extend 40)\"} $zext.bv8.bv48(i: bv8) returns (bv48);");
  D("function {:bvbuiltin \"(_ zero_extend 48)\"} $zext.bv8.bv56(i: bv8) returns (bv56);");
  D("function {:bvbuiltin \"(_ zero_extend 56)\"} $zext.bv8.bv64(i: bv8) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 80)\"} $zext.bv8.bv88(i: bv8) returns (bv88);");
  D("function {:bvbuiltin \"(_ zero_extend 88)\"} $zext.bv8.bv96(i: bv8) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 120)\"} $zext.bv8.bv128(i: bv8) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv16.bv24(i: bv16) returns (bv24);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv16.bv32(i: bv16) returns (bv32);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv16.bv40(i: bv16) returns (bv40);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv16.bv48(i: bv16) returns (bv48);");
  D("function {:bvbuiltin \"(_ zero_extend 40)\"} $zext.bv16.bv56(i: bv16) returns (bv56);");
  D("function {:bvbuiltin \"(_ zero_extend 48)\"} $zext.bv16.bv64(i: bv16) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 72)\"} $zext.bv16.bv88(i: bv16) returns (bv88);");
  D("function {:bvbuiltin \"(_ zero_extend 80)\"} $zext.bv16.bv96(i: bv16) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 112)\"} $zext.bv16.bv128(i: bv16) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv24.bv32(i: bv24) returns (bv32);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv24.bv40(i: bv24) returns (bv40);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv24.bv48(i: bv24) returns (bv48);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv24.bv56(i: bv24) returns (bv56);");
  D("function {:bvbuiltin \"(_ zero_extend 40)\"} $zext.bv24.bv64(i: bv24) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 64)\"} $zext.bv24.bv88(i: bv24) returns (bv88);");
  D("function {:bvbuiltin \"(_ zero_extend 72)\"} $zext.bv24.bv96(i: bv24) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 104)\"} $zext.bv24.bv128(i: bv24) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv32.bv40(i: bv32) returns (bv40);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv32.bv48(i: bv32) returns (bv48);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv32.bv56(i: bv32) returns (bv56);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv32.bv64(i: bv32) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 56)\"} $zext.bv32.bv88(i: bv32) returns (bv88);");
  D("function {:bvbuiltin \"(_ zero_extend 64)\"} $zext.bv32.bv96(i: bv32) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 96)\"} $zext.bv32.bv128(i: bv32) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv40.bv48(i: bv40) returns (bv48);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv40.bv56(i: bv40) returns (bv56);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv40.bv64(i: bv40) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 48)\"} $zext.bv40.bv88(i: bv40) returns (bv88);");
  D("function {:bvbuiltin \"(_ zero_extend 56)\"} $zext.bv40.bv96(i: bv40) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 88)\"} $zext.bv40.bv128(i: bv40) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 16)\"} $zext.bv48.bv64(i: bv48) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 40)\"} $zext.bv48.bv88(i: bv48) returns (bv88);");
  D("function {:bvbuiltin \"(_ zero_extend 48)\"} $zext.bv48.bv96(i: bv48) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 80)\"} $zext.bv48.bv128(i: bv48) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv56.bv64(i: bv56) returns (bv64);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv56.bv88(i: bv56) returns (bv88);");
  D("function {:bvbuiltin \"(_ zero_extend 40)\"} $zext.bv56.bv96(i: bv56) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 72)\"} $zext.bv56.bv128(i: bv56) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 24)\"} $zext.bv64.bv88(i: bv64) returns (bv88);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv64.bv96(i: bv64) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 64)\"} $zext.bv64.bv128(i: bv64) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 8)\"} $zext.bv88.bv96(i: bv88) returns (bv96);");
  D("function {:bvbuiltin \"(_ zero_extend 40)\"} $zext.bv88.bv128(i: bv88) returns (bv128);");
  D("function {:bvbuiltin \"(_ zero_extend 32)\"} $zext.bv96.bv128(i: bv96) returns (bv128);");

  DECLARE(INLINE_CONVERSION,bv1,bv8,$sext,{if i == 0bv1 then 0bv8 else 255bv8});
  DECLARE(INLINE_CONVERSION,bv1,bv16,$sext,{if i == 0bv1 then 0bv16 else 65535bv16});
  DECLARE(INLINE_CONVERSION,bv1,bv24,$sext,{if i == 0bv1 then 0bv24 else 16777215bv24});
  DECLARE(INLINE_CONVERSION,bv1,bv32,$sext,{if i == 0bv1 then 0bv32 else 4294967295bv32});
  DECLARE(INLINE_CONVERSION,bv1,bv40,$sext,{if i == 0bv1 then 0bv40 else 1099511627775bv40});
  DECLARE(INLINE_CONVERSION,bv1,bv48,$sext,{if i == 0bv1 then 0bv48 else 281474976710655bv48});
  DECLARE(INLINE_CONVERSION,bv1,bv56,$sext,{if i == 0bv1 then 0bv56 else 72057594037927935bv56});
  DECLARE(INLINE_CONVERSION,bv1,bv64,$sext,{if i == 0bv1 then 0bv64 else 18446744073709551615bv64});
  DECLARE(INLINE_CONVERSION,bv1,bv88,$sext,{if i == 0bv1 then 0bv88 else 309485009821345068724781055bv88});
  DECLARE(INLINE_CONVERSION,bv1,bv96,$sext,{if i == 0bv1 then 0bv96 else 79228162514264337593543950335bv96});
  DECLARE(INLINE_CONVERSION,bv1,bv128,$sext,{if i == 0bv1 then 0bv128 else 340282366920938463463374607431768211455bv128});
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv8.bv16(i: bv8) returns (bv16);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv8.bv24(i: bv8) returns (bv24);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv8.bv32(i: bv8) returns (bv32);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv8.bv40(i: bv8) returns (bv40);");
  D("function {:bvbuiltin \"(_ sign_extend 40)\"} $sext.bv8.bv48(i: bv8) returns (bv48);");
  D("function {:bvbuiltin \"(_ sign_extend 48)\"} $sext.bv8.bv56(i: bv8) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 56)\"} $sext.bv8.bv64(i: bv8) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 80)\"} $sext.bv8.bv88(i: bv8) returns (bv88);");
  D("function {:bvbuiltin \"(_ sign_extend 88)\"} $sext.bv8.bv96(i: bv8) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 120)\"} $sext.bv8.bv128(i: bv8) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv16.bv24(i: bv16) returns (bv24);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv16.bv32(i: bv16) returns (bv32);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv16.bv40(i: bv16) returns (bv40);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv16.bv48(i: bv16) returns (bv48);");
  D("function {:bvbuiltin \"(_ sign_extend 40)\"} $sext.bv16.bv56(i: bv16) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 48)\"} $sext.bv16.bv64(i: bv16) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 72)\"} $sext.bv16.bv88(i: bv16) returns (bv88);");
  D("function {:bvbuiltin \"(_ sign_extend 80)\"} $sext.bv16.bv96(i: bv16) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 112)\"} $sext.bv16.bv128(i: bv16) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv24.bv32(i: bv24) returns (bv32);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv24.bv40(i: bv24) returns (bv40);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv24.bv48(i: bv24) returns (bv48);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv24.bv56(i: bv24) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 40)\"} $sext.bv24.bv64(i: bv24) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 64)\"} $sext.bv24.bv88(i: bv24) returns (bv88);");
  D("function {:bvbuiltin \"(_ sign_extend 72)\"} $sext.bv24.bv96(i: bv24) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 104)\"} $sext.bv24.bv128(i: bv24) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv32.bv40(i: bv32) returns (bv40);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv32.bv48(i: bv32) returns (bv48);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv32.bv56(i: bv32) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv32.bv64(i: bv32) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 56)\"} $sext.bv32.bv88(i: bv32) returns (bv88);");
  D("function {:bvbuiltin \"(_ sign_extend 64)\"} $sext.bv32.bv96(i: bv32) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 96)\"} $sext.bv32.bv128(i: bv32) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv40.bv48(i: bv40) returns (bv48);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv40.bv56(i: bv40) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv40.bv64(i: bv40) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 48)\"} $sext.bv40.bv88(i: bv40) returns (bv88);");
  D("function {:bvbuiltin \"(_ sign_extend 56)\"} $sext.bv40.bv96(i: bv40) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 88)\"} $sext.bv40.bv128(i: bv40) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv48.bv56(i: bv48) returns (bv56);");
  D("function {:bvbuiltin \"(_ sign_extend 16)\"} $sext.bv48.bv64(i: bv48) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 40)\"} $sext.bv48.bv88(i: bv48) returns (bv88);");
  D("function {:bvbuiltin \"(_ sign_extend 48)\"} $sext.bv48.bv96(i: bv48) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 80)\"} $sext.bv48.bv128(i: bv48) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv56.bv64(i: bv56) returns (bv64);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv56.bv88(i: bv56) returns (bv88);");
  D("function {:bvbuiltin \"(_ sign_extend 40)\"} $sext.bv56.bv96(i: bv56) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 72)\"} $sext.bv56.bv128(i: bv56) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 24)\"} $sext.bv64.bv88(i: bv64) returns (bv88);");
  D("function {:bvbuiltin \"(_ sign_extend 32)\"} $sext.bv64.bv96(i: bv64) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 64)\"} $sext.bv64.bv128(i: bv64) returns (bv128);");
  D("function {:bvbuiltin \"(_ sign_extend 8)\"} $sext.bv88.bv96(i: bv88) returns (bv96);");
  D("function {:bvbuiltin \"(_ sign_extend 40)\"} $sext.bv88.bv128(i: bv88) returns (bv128);");
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

  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $eq, {i1 == i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ne, {i1 != i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ule, {i1 <= i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ult, {i1 < i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $uge, {i1 >= i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $ugt, {i1 > i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $sle, {i1 <= i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $slt, {i1 < i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $sge, {i1 >= i2})
  DECLARE_EACH_INT_TYPE(INLINE_BINARY_PRED, $sgt, {i1 > i2})

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
  D("axiom($and.i32(32, 16) == 0);");

  DECLARE_INT_TRUNCS
  DECLARE_INT_ZEXTS
  DECLARE_INT_SEXTS

  //Non bit-precise modeling of floating-points

  D("function $fp(ipart:int, fpart:int, epart:int) returns (float);");
  DECLARE(UNINTERPRETED_BINARY_OP,float,$fadd);
  DECLARE(UNINTERPRETED_BINARY_OP,float,$fsub);
  DECLARE(UNINTERPRETED_BINARY_OP,float,$fmul);
  DECLARE(UNINTERPRETED_BINARY_OP,float,$fdiv);
  DECLARE(UNINTERPRETED_BINARY_OP,float,$frem);
  DECLARE(INLINE_BINARY_COMP,float,$ffalse,{false});
  DECLARE(INLINE_BINARY_COMP,float,$ftrue,{true});
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$foeq);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$foge);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$fogt);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$fole);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$folt);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$fone);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$ford);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$fueq);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$fuge);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$fugt);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$fule);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$fult);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$fune);
  DECLARE(UNINTERPRETED_BINARY_COMP,float,$funo);

  DECLARE(UNINTERPRETED_CONVERSION,float,i128,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i128,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,i96,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i96,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,i88,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i88,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,i64,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i64,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,i56,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i56,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,i48,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i48,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,i40,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i40,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,i32,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i32,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,i24,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i24,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,i16,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i16,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,i8,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,i8,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,i128,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i128,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i96,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i96,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i88,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i88,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i64,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i64,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i56,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i56,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i48,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i48,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i40,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i40,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i32,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i32,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i24,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i24,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i16,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i16,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i8,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,i8,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv128,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv128,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv96,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv96,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv88,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv88,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv64,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv64,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv56,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv56,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv48,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv48,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv40,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv40,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv32,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv32,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv24,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv24,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv16,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv16,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv8,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv8,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bv128,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv128,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv96,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv96,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv88,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv88,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv64,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv64,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv56,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv56,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv48,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv48,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv40,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv40,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv32,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv32,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv24,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv24,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv16,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv16,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv8,float,$si2fp);
  DECLARE(UNINTERPRETED_CONVERSION,bv8,float,$ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION,float,float,$fptrunc);
  DECLARE(UNINTERPRETED_CONVERSION,float,float,$fpext);
  DECLARE(UNINTERPRETED_CONVERSION,float,i8,$bitcast);
  DECLARE(UNINTERPRETED_CONVERSION,float,bv8,$bitcast);
  DECLARE(UNINTERPRETED_CONVERSION,i8,float,$bitcast);
  DECLARE(UNINTERPRETED_CONVERSION,bv8,float,$bitcast);

#ifndef NO_FORALL
  D("axiom (forall f1, f2: float :: $foeq.float.bool(f1,f2) <==> !$fune.float.bool(f1,f2));");
  D("axiom (forall f1, f2: float :: $fone.float.bool(f1,f2) <==> !$fueq.float.bool(f1,f2));");
  D("axiom (forall f1, f2: float :: $fogt.float.bool(f1,f2) <==> !$fule.float.bool(f1,f2));");
  D("axiom (forall f1, f2: float :: $foge.float.bool(f1,f2) <==> !$fult.float.bool(f1,f2));");
  D("axiom (forall f1, f2: float :: $folt.float.bool(f1,f2) <==> !$fuge.float.bool(f1,f2));");
  D("axiom (forall f1, f2: float :: $fole.float.bool(f1,f2) <==> !$fugt.float.bool(f1,f2));");
  D("axiom (forall f1, f2: float :: $ford.float.bool(f1,f2) <==> !$funo.float.bool(f1,f2));");
  D("axiom (forall f: float, i: i8 :: $bitcast.float.i8(f) == i <==> $bitcast.i8.float(i) == f);");
  // TODO: add proper axiom for float/bv8 conversions
#endif

#if FLOAT_ENABLED
  // Bit-precise modeling of floating-points

  // Boogie built-in arithmetic
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_OP, $fadd, {i1 + i2})
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_OP, $fsub, {i1 - i2})
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_OP, $fmul, {i1 * i2})
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_OP, $fdiv, {i1 / i2})

  // FP arithmetic
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_UNARY_OP, $abs, fp.abs)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_UNARY_OP, $sqrt, fp.sqrt)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_BINARY_OP, $fma, fp.fma)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_BINARY_OP, $frem, fp.rem)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_BINARY_OP, $min, fp.min)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_BINARY_OP, $max, fp.max)

  // FP value predicates
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_UNARY_PRED, $isnormal, fp.isNormal)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_UNARY_PRED, $issubnormal, fp.isSubnormal)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_UNARY_PRED, $iszero, fp.isZero)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_UNARY_PRED, $isinfinite, fp.isInfinite)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_UNARY_PRED, $isnan, fp.isNaN)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_UNARY_PRED, $isnegative, fp.isNegative)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_UNARY_PRED, $ispositive, fp.isPositive)

  // FP comparison predicates
  // I assume fp.eq is exactly ieee compareQuietEqual
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_BINARY_COMP, $foeq, fp.eq)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_BINARY_COMP, $fole, fp.leq)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_BINARY_COMP, $folt, fp.lt)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_BINARY_COMP, $foge, fp.geq)
  DECLARE_EACH_FLOAT_TYPE(BUILTIN_BINARY_COMP, $fogt, fp.gt)
  D("function {:inline} $fone.bvhalf.bool(f1:bvhalf, f2:bvhalf) returns (bool) {!$fueq.bvhalf.bool(f1,f2)}");
  D("function {:inline} $fone.bvfloat.bool(f1:bvfloat, f2:bvfloat) returns (bool) {!$fueq.bvfloat.bool(f1,f2)}");
  D("function {:inline} $fone.bvdouble.bool(f1:bvdouble, f2:bvdouble) returns (bool) {!$fueq.bvdouble.bool(f1,f2)}");
  D("function {:inline} $ford.bvhalf.bool(f1:bvhalf, f2:bvhalf) returns (bool) {!$funo.bvhalf.bool(f1,f2)}");
  D("function {:inline} $ford.bvfloat.bool(f1:bvfloat, f2:bvfloat) returns (bool) {!$funo.bvfloat.bool(f1,f2)}");
  D("function {:inline} $ford.bvdouble.bool(f1:bvdouble, f2:bvdouble) returns (bool) {!$funo.bvdouble.bool(f1,f2)}");
  D("function {:inline} $fueq.bvhalf.bool(f1:bvhalf, f2:bvhalf) returns (bool) {$isnan.bvhalf.bool(f1)||$isnan.bvhalf.bool(f2)||$foeq.bvhalf.bool(f1,f2)}");
  D("function {:inline} $fugt.bvhalf.bool(f1:bvhalf, f2:bvhalf) returns (bool) {$isnan.bvhalf.bool(f1)||$isnan.bvhalf.bool(f2)||$fogt.bvhalf.bool(f1,f2)}");
  D("function {:inline} $fuge.bvhalf.bool(f1:bvhalf, f2:bvhalf) returns (bool) {$isnan.bvhalf.bool(f1)||$isnan.bvhalf.bool(f2)||$foge.bvhalf.bool(f1,f2)}");
  D("function {:inline} $fult.bvhalf.bool(f1:bvhalf, f2:bvhalf) returns (bool) {$isnan.bvhalf.bool(f1)||$isnan.bvhalf.bool(f2)||$folt.bvhalf.bool(f1,f2)}");
  D("function {:inline} $fule.bvhalf.bool(f1:bvhalf, f2:bvhalf) returns (bool) {$isnan.bvhalf.bool(f1)||$isnan.bvhalf.bool(f2)||$fole.bvhalf.bool(f1,f2)}");
  D("function {:inline} $fune.bvhalf.bool(f1:bvhalf, f2:bvhalf) returns (bool) {$isnan.bvhalf.bool(f1)||$isnan.bvhalf.bool(f2)||$fone.bvhalf.bool(f1,f2)}");
  D("function {:inline} $funo.bvhalf.bool(f1:bvhalf, f2:bvhalf) returns (bool) {$isnan.bvhalf.bool(f1)||$isnan.bvhalf.bool(f2)}");
  D("function {:inline} $fueq.bvfloat.bool(f1:bvfloat, f2:bvfloat) returns (bool) {$isnan.bvfloat.bool(f1)||$isnan.bvfloat.bool(f2)||$foeq.bvfloat.bool(f1,f2)}");
  D("function {:inline} $fugt.bvfloat.bool(f1:bvfloat, f2:bvfloat) returns (bool) {$isnan.bvfloat.bool(f1)||$isnan.bvfloat.bool(f2)||$fogt.bvfloat.bool(f1,f2)}");
  D("function {:inline} $fuge.bvfloat.bool(f1:bvfloat, f2:bvfloat) returns (bool) {$isnan.bvfloat.bool(f1)||$isnan.bvfloat.bool(f2)||$foge.bvfloat.bool(f1,f2)}");
  D("function {:inline} $fult.bvfloat.bool(f1:bvfloat, f2:bvfloat) returns (bool) {$isnan.bvfloat.bool(f1)||$isnan.bvfloat.bool(f2)||$folt.bvfloat.bool(f1,f2)}");
  D("function {:inline} $fule.bvfloat.bool(f1:bvfloat, f2:bvfloat) returns (bool) {$isnan.bvfloat.bool(f1)||$isnan.bvfloat.bool(f2)||$fole.bvfloat.bool(f1,f2)}");
  D("function {:inline} $fune.bvfloat.bool(f1:bvfloat, f2:bvfloat) returns (bool) {$isnan.bvfloat.bool(f1)||$isnan.bvfloat.bool(f2)||$fone.bvfloat.bool(f1,f2)}");
  D("function {:inline} $funo.bvfloat.bool(f1:bvfloat, f2:bvfloat) returns (bool) {$isnan.bvfloat.bool(f1)||$isnan.bvfloat.bool(f2)}");
  D("function {:inline} $fueq.bvdouble.bool(f1:bvdouble, f2:bvdouble) returns (bool) {$isnan.bvdouble.bool(f1)||$isnan.bvdouble.bool(f2)||$foeq.bvdouble.bool(f1,f2)}");
  D("function {:inline} $fugt.bvdouble.bool(f1:bvdouble, f2:bvdouble) returns (bool) {$isnan.bvdouble.bool(f1)||$isnan.bvdouble.bool(f2)||$fogt.bvdouble.bool(f1,f2)}");
  D("function {:inline} $fuge.bvdouble.bool(f1:bvdouble, f2:bvdouble) returns (bool) {$isnan.bvdouble.bool(f1)||$isnan.bvdouble.bool(f2)||$foge.bvdouble.bool(f1,f2)}");
  D("function {:inline} $fult.bvdouble.bool(f1:bvdouble, f2:bvdouble) returns (bool) {$isnan.bvdouble.bool(f1)||$isnan.bvdouble.bool(f2)||$folt.bvdouble.bool(f1,f2)}");
  D("function {:inline} $fule.bvdouble.bool(f1:bvdouble, f2:bvdouble) returns (bool) {$isnan.bvdouble.bool(f1)||$isnan.bvdouble.bool(f2)||$fole.bvdouble.bool(f1,f2)}");
  D("function {:inline} $fune.bvdouble.bool(f1:bvdouble, f2:bvdouble) returns (bool) {$isnan.bvdouble.bool(f1)||$isnan.bvdouble.bool(f2)||$fone.bvdouble.bool(f1,f2)}");
  D("function {:inline} $funo.bvdouble.bool(f1:bvdouble, f2:bvdouble) returns (bool) {$isnan.bvdouble.bool(f1)||$isnan.bvdouble.bool(f2)}");
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_COMP, $ffalse, {false})
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_COMP, $ftrue, {true})

  D("function {:builtin \"(_ to_fp 8 24) RNE\"} dtf(bvdouble) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ftd(bvfloat) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ltf(bvlongdouble) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ltd(bvlongdouble) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 15 65) RNE\"} ftl(bvfloat) returns (bvlongdouble);");
  D("function {:builtin \"(_ to_fp 15 65) RNE\"} dtl(bvdouble) returns (bvlongdouble);");
  DECLARE(INLINE_CONVERSION,bvdouble,bvfloat,$fptrunc,{dtf(i)});
  DECLARE(INLINE_CONVERSION,bvfloat,bvdouble,$fpext,{ftd(i)});
  DECLARE(INLINE_CONVERSION,bvlongdouble,bvfloat,$fptrunc,{ltf(i)});
  DECLARE(INLINE_CONVERSION,bvlongdouble,bvdouble,$fptrunc,{ltd(i)});
  DECLARE(INLINE_CONVERSION,bvfloat,bvlongdouble,$fpext,{ftl(i)});
  DECLARE(INLINE_CONVERSION,bvdouble,bvlongdouble,$fpext,{dtl(i)});

  // Add truncation for default casts to int
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv128,$fp2si,(_ fp.to_sbv 128) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv96,$fp2si,(_ fp.to_sbv 96) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv88,$fp2si,(_ fp.to_sbv 88) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv64,$fp2si,(_ fp.to_sbv 64) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv56,$fp2si,(_ fp.to_sbv 56) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv48,$fp2si,(_ fp.to_sbv 48) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv40,$fp2si,(_ fp.to_sbv 40) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv32,$fp2si,(_ fp.to_sbv 32) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv24,$fp2si,(_ fp.to_sbv 24) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv16,$fp2si,(_ fp.to_sbv 16) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv8,$fp2si,(_ fp.to_sbv 8) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv1,$fp2si,(_ fp.to_sbv 1) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv128,$fp2ui,(_ fp.to_ubv 128) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv96,$fp2ui,(_ fp.to_ubv 96) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv88,$fp2ui,(_ fp.to_ubv 88) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv64,$fp2ui,(_ fp.to_ubv 64) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv56,$fp2ui,(_ fp.to_ubv 56) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv48,$fp2ui,(_ fp.to_ubv 48) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv40,$fp2ui,(_ fp.to_ubv 40) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv32,$fp2ui,(_ fp.to_ubv 32) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv24,$fp2ui,(_ fp.to_ubv 24) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv16,$fp2ui,(_ fp.to_ubv 16) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv8,$fp2ui,(_ fp.to_ubv 8) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvfloat,bv1,$fp2ui,(_ fp.to_ubv 1) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv128,$fp2si,(_ fp.to_sbv 128) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv96,$fp2si,(_ fp.to_sbv 96) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv88,$fp2si,(_ fp.to_sbv 88) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv64,$fp2si,(_ fp.to_sbv 64) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv56,$fp2si,(_ fp.to_sbv 56) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv48,$fp2si,(_ fp.to_sbv 48) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv40,$fp2si,(_ fp.to_sbv 40) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv32,$fp2si,(_ fp.to_sbv 32) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv24,$fp2si,(_ fp.to_sbv 24) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv16,$fp2si,(_ fp.to_sbv 16) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv8,$fp2si,(_ fp.to_sbv 8) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv1,$fp2si,(_ fp.to_sbv 1) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv128,$fp2ui,(_ fp.to_ubv 128) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv96,$fp2ui,(_ fp.to_ubv 96) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv88,$fp2ui,(_ fp.to_ubv 88) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv64,$fp2ui,(_ fp.to_ubv 64) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv56,$fp2ui,(_ fp.to_ubv 56) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv48,$fp2ui,(_ fp.to_ubv 48) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv40,$fp2ui,(_ fp.to_ubv 40) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv32,$fp2ui,(_ fp.to_ubv 32) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv24,$fp2ui,(_ fp.to_ubv 24) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv16,$fp2ui,(_ fp.to_ubv 16) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv8,$fp2ui,(_ fp.to_ubv 8) RTZ);
  DECLARE(BUILTIN_CONVERSION,bvdouble,bv1,$fp2ui,(_ fp.to_ubv 1) RTZ);
  // Warning: do we need bv2int cast here?
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i128,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i96,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i88,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i64,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i56,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i48,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i40,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i32,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i24,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i16,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i8,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i1,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i128,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i96,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i88,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i64,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i56,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i48,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i40,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i32,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i24,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i16,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i8,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i1,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i128,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i96,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i88,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i64,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i56,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i48,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i40,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i32,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i24,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i16,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i8,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i1,$fp2si);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i128,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i96,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i88,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i64,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i56,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i48,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i40,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i32,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i24,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i16,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i8,$fp2ui);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i1,$fp2ui);
  // Warning: undefined behaviors can occur
  // https://llvm.org/docs/LangRef.html#uitofp-to-instruction
  DECLARE(BUILTIN_CONVERSION, bv128, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv96, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv88, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv64, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv56, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv48, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv40, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv32, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv24, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv16, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv8, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv1, bvfloat, $ui2fp,(_ to_fp_unsigned 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv128, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv96, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv88, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv64, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv56, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv48, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv40, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv32, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv24, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv16, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv8, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv1, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, bv128, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv96, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv88, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv64, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv56, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv48, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv40, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv32, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv24, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv16, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv8, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv1, bvdouble, $ui2fp,(_ to_fp_unsigned 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv128, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv96, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv88, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv64, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv56, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv48, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv40, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv32, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv24, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv16, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv8, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, bv1, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  // Warning: integer-encoding fixes needed here
  DECLARE(UNINTERPRETED_CONVERSION, i128, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i96, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i88, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i64, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i56, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i48, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i40, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i32, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i24, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i16, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i8, bvfloat, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i1, bvfloat, $ui2fp);
  DECLARE(BUILTIN_CONVERSION, i128, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i96, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i88, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i64, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i56, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i48, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i40, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i32, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i24, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i16, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i8, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(BUILTIN_CONVERSION, i1, bvfloat, $si2fp,(_ to_fp 8 24) RNE);
  DECLARE(UNINTERPRETED_CONVERSION, i128, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i96, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i88, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i64, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i56, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i48, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i40, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i32, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i24, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i16, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i8, bvdouble, $ui2fp);
  DECLARE(UNINTERPRETED_CONVERSION, i1, bvdouble, $ui2fp);
  DECLARE(BUILTIN_CONVERSION, i128, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i96, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i88, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i64, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i56, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i48, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i40, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i32, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i24, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i16, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i8, bvdouble, $si2fp,(_ to_fp 11 53) RNE);
  DECLARE(BUILTIN_CONVERSION, i1, bvdouble, $si2fp,(_ to_fp 11 53) RNE);

  D("function {:builtin \"fp.roundToIntegral RNE\"} $round.rne.bvfloat(bvfloat) returns (bvfloat);");
  D("function {:builtin \"fp.roundToIntegral RNA\"} $round.rna.bvfloat(bvfloat) returns (bvfloat);");
  D("function {:builtin \"fp.roundToIntegral RTP\"} $ceil.bvfloat(bvfloat) returns (bvfloat);");
  D("function {:builtin \"fp.roundToIntegral RTN\"} $floor.bvfloat(bvfloat) returns (bvfloat);");
  D("function {:builtin \"fp.roundToIntegral RTZ\"} $trunc.bvfloat(bvfloat) returns (bvfloat);");
  D("function {:builtin \"fp.roundToIntegral RNE\"} $round.rne.bvdouble(bvdouble) returns (bvdouble);");
  D("function {:builtin \"fp.roundToIntegral RNA\"} $round.rna.bvdouble(bvdouble) returns (bvdouble);");
  D("function {:builtin \"fp.roundToIntegral RTP\"} $ceil.bvdouble(bvdouble) returns (bvdouble);");
  D("function {:builtin \"fp.roundToIntegral RTN\"} $floor.bvdouble(bvdouble) returns (bvdouble);");
  D("function {:builtin \"fp.roundToIntegral RTZ\"} $trunc.bvdouble(bvdouble) returns (bvdouble);");

  #if BUILD_64
    D("function {:builtin \"(_ fp.to_sbv 64) RNA\"} $lround.bvfloat(bvfloat) returns (bv64);");
    D("function {:builtin \"(_ fp.to_sbv 64) RNA\"} $lround.bvdouble(bvdouble) returns (bv64);");

  #else
    D("function {:builtin \"(_ fp.to_sbv 32) RNA\"} $lround.bvfloat(bvfloat) returns (bv32);");
    D("function {:builtin \"(_ fp.to_sbv 32) RNA\"} $lround.bvdouble(bvdouble) returns (bv32);");
  #endif

#endif

  // Memory Model
  D("const $GLOBALS_BOTTOM: ref;");
  D("const $EXTERNS_BOTTOM: ref;");
  D("const $MALLOC_TOP: ref;");
  D("function {:inline} $isExternal(p: ref) returns (bool) {$slt.ref.bool(p,$EXTERNS_BOTTOM)}");

  DECLARE_EACH_INT_TYPE(SAFE_LOAD_OP, $load, { M[p] })
  DECLARE_EACH_BV_TYPE(SAFE_LOAD_OP, $load, { M[p] })
  DECLARE_UNSAFE_LOADS
  DECLARE(UNSAFE_LOAD_OP, bv8, $load.bytes, { M[p] });
  DECLARE(UNSAFE_LOAD_OP, bv1, $load.bytes, { $trunc.bv8.bv1(M[p]) });

  DECLARE_EACH_INT_TYPE(SAFE_STORE_OP, $store, { M[p := v] })
  DECLARE_EACH_BV_TYPE(SAFE_STORE_OP, $store, { M[p := v] })
  DECLARE_UNSAFE_STORES
  DECLARE(UNSAFE_STORE_OP, bv8, $store.bytes, {M[p := v]});
  DECLARE(UNSAFE_STORE_OP, bv1, $store.bytes, {M[p := $zext.bv1.bv8(v)]});

  D("function {:inline} $load.ref(M: [ref] ref, p: ref) returns (ref) { M[p] }");
  D("function {:inline} $store.ref(M: [ref] ref, p: ref, v: ref) returns ([ref] ref) { M[p := v] }");

  D("function {:inline} $load.float(M: [ref] float, p: ref) returns (float) { M[p] }");
  D("function {:inline} $load.unsafe.float(M: [ref] i8, p: ref) returns (float) { $bitcast.i8.float(M[p]) }");
  D("function {:inline} $store.float(M: [ref] float, p: ref, v: float) returns ([ref] float) { M[p := v] }");
  D("function {:inline} $store.unsafe.float(M: [ref] i8, p: ref, v: float) returns ([ref] i8) { M[p := $bitcast.float.i8(v)] }");
  D("function {:inline} $load.bytes.float(M: [ref] bv8, p: ref) returns (float) { $bitcast.bv8.float(M[p]) }");
  D("function {:inline} $store.bytes.float(M:[ref]bv8, p:ref, v:float) returns ([ref]bv8) {M[p := $bitcast.float.bv8(v)]}");

  #if FLOAT_ENABLED
  DECLARE(UNINTERPRETED_CONVERSION,bvhalf,bv16,$bitcast);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,bv32,$bitcast);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,bv64,$bitcast);
  DECLARE(BUILTIN_CONVERSION,bv16,bvhalf,$bitcast,(_ to_fp 5 11));
  DECLARE(BUILTIN_CONVERSION,bv32,bvfloat,$bitcast,(_ to_fp 8 24));
  DECLARE(BUILTIN_CONVERSION,bv64,bvdouble,$bitcast,(_ to_fp 11 53));
  DECLARE(UNINTERPRETED_CONVERSION,bvhalf,i16,$bitcast);
  DECLARE(UNINTERPRETED_CONVERSION,bvfloat,i32,$bitcast);
  DECLARE(UNINTERPRETED_CONVERSION,bvdouble,i64,$bitcast);
  DECLARE(UNINTERPRETED_CONVERSION,i16,bvhalf,$bitcast);
  DECLARE(UNINTERPRETED_CONVERSION,i32,bvfloat,$bitcast);
  DECLARE(UNINTERPRETED_CONVERSION,i64,bvdouble,$bitcast);
  D("axiom (forall f: bvhalf :: $bitcast.bv16.bvhalf($bitcast.bvhalf.bv16(f)) == f);");
  D("axiom (forall f: bvfloat :: $bitcast.bv32.bvfloat($bitcast.bvfloat.bv32(f)) == f);");
  D("axiom (forall f: bvdouble :: $bitcast.bv64.bvdouble($bitcast.bvdouble.bv64(f)) == f);");
  //D("axiom (forall b: bv16 :: b[15:10] == 31bv5 && b[10:0] != 0bv10 ==> $bitcast.bvhalf.bv16($bitcast.bv16.bvhalf(b)) == b);");
  //D("axiom (forall b: bv32 :: b[31:23] == 255bv8 && b[23:0] != 0bv23 ==> $bitcast.bvfloat.bv32($bitcast.bv32.bvfloat(b)) == b);");
  //D("axiom (forall b: bv64 :: b[63:52] == 2047bv11 && b[52:0] != 0bv52 ==> $bitcast.bvdouble.bv64($bitcast.bv64.bvdouble(b)) == b);");
  // TODO: add more constraints

  D("axiom (forall f: bvfloat :: dtf(ftd(f)) == f);");

  D("axiom (forall f: bvhalf, i: i16 :: $bitcast.bvhalf.i16(f) == i <==> $bitcast.i16.bvhalf(i) == f);");
  D("axiom (forall f: bvfloat, i: i32 :: $bitcast.bvfloat.i32(f) == i <==> $bitcast.i32.bvfloat(i) == f);");
  D("axiom (forall f: bvdouble, i: i64 :: $bitcast.bvdouble.i64(f) == i <==> $bitcast.i64.bvdouble(i) == f);");

  D("function {:inline} $load.bvhalf(M: [ref] bvhalf, p: ref) returns (bvhalf) { M[p] }");
  D("function {:inline} $store.bvhalf(M: [ref] bvhalf, p: ref, v: bvhalf) returns ([ref] bvhalf) { M[p := v] }");
  D("function {:inline} $load.bvfloat(M: [ref] bvfloat, p: ref) returns (bvfloat) { M[p] }");
  D("function {:inline} $store.bvfloat(M: [ref] bvfloat, p: ref, v: bvfloat) returns ([ref] bvfloat) { M[p := v] }");
  D("function {:inline} $load.bvdouble(M: [ref] bvdouble, p: ref) returns (bvdouble) { M[p] }");
  D("function {:inline} $store.bvdouble(M: [ref] bvdouble, p: ref, v: bvdouble) returns ([ref] bvdouble) { M[p := v] }");

  D("function {:inline} $store.bytes.bvhalf(M:[ref]bv8, p:ref, v:bvhalf) returns ([ref]bv8) {"
    "$store.bytes.bv16(M, p, $bitcast.bvhalf.bv16(v))}");
  D("function {:inline} $store.bytes.bvfloat(M:[ref]bv8, p:ref, v:bvfloat) returns ([ref]bv8) {"
    "$store.bytes.bv32(M, p, $bitcast.bvfloat.bv32(v))}");
  D("function {:inline} $store.bytes.bvdouble(M:[ref]bv8, p:ref, v:bvdouble) returns ([ref]bv8) {"
    "$store.bytes.bv64(M, p, $bitcast.bvdouble.bv64(v))}");
  D("function {:inline} $store.unsafe.bvhalf(M:[ref]i8, p:ref, v:bvhalf) returns ([ref]i8) {"
    "$store.i16(M, p, $bitcast.bvhalf.i16(v))}");
  D("function {:inline} $store.unsafe.bvfloat(M:[ref]i8, p:ref, v:bvfloat) returns ([ref]i8) {"
    "$store.i32(M, p, $bitcast.bvfloat.i32(v))}");
  D("function {:inline} $store.unsafe.bvdouble(M:[ref]i8, p:ref, v:bvdouble) returns ([ref]i8) {"
    "$store.i64(M, p, $bitcast.bvdouble.i64(v))}");

  D("function {:inline} $load.bytes.bvhalf(M: [ref] bv8, p: ref) returns (bvhalf) {"
    "$bitcast.bv16.bvhalf($load.bytes.bv16(M, p))}");
  D("function {:inline} $load.bytes.bvfloat(M: [ref] bv8, p: ref) returns (bvfloat) {"
    "$bitcast.bv32.bvfloat($load.bytes.bv32(M, p))}");
  D("function {:inline} $load.bytes.bvdouble(M: [ref] bv8, p: ref) returns (bvdouble) {"
    "$bitcast.bv64.bvdouble($load.bytes.bv64(M, p))}");
  D("function {:inline} $load.unsafe.bvhalf(M: [ref] i8, p: ref) returns (bvhalf) {"
    "$bitcast.i16.bvhalf($load.i16(M, p))}");
  D("function {:inline} $load.unsafe.bvfloat(M: [ref] i8, p: ref) returns (bvfloat) {"
    "$bitcast.i32.bvfloat($load.i32(M, p))}");
  D("function {:inline} $load.unsafe.bvdouble(M: [ref] i8, p: ref) returns (bvdouble) {"
    "$bitcast.i64.bvdouble($load.i64(M, p))}");
  #endif

  // Memory debugging symbols
  D("type $mop;");
  D("procedure boogie_si_record_mop(m: $mop);");
  D("const $MOP: $mop;");

  D("var $exn: bool;");
  D("var $exnv: int;");
  D("function $extractvalue(p: int, i: int) returns (int);\n");

  D("procedure $alloc(n: ref) returns (p: ref)\n"
    "{\n"
    "  call p := $$alloc(n);\n"
    "}\n");

#if MEMORY_SAFETY
  D("function $base(ref) returns (ref);");
  D("var $allocatedCounter: int;\n");

  D("procedure $malloc(n: ref) returns (p: ref)\n"
    "modifies $allocatedCounter;\n"
    "{\n"
    "  if ($ne.ref.bool(n, $0.ref)) {\n"
    "    $allocatedCounter := $allocatedCounter + 1;\n"
    "  }\n"
    "  call p := $$alloc(n);\n"
    "}\n");

#if MEMORY_MODEL_NO_REUSE_IMPLS
  D("var $Alloc: [ref] bool;");
  D("function $Size(ref) returns (ref);");
  D("var $CurrAddr:ref;\n");

  D("procedure $galloc(base_addr: ref, size: ref)\n"
    "{\n"
    "  assume $Size(base_addr) == size;\n"
    "  assume (forall addr: ref :: {$base(addr)} $sle.ref.bool(base_addr, addr) && $slt.ref.bool(addr, $add.ref(base_addr, size)) ==> $base(addr) == base_addr);\n"
    "  $Alloc[base_addr] := true;\n"
    "}\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref)\n"
    "modifies $Alloc, $CurrAddr;\n"
    "{\n"
    "  assume $sle.ref.bool($0.ref, n);\n"
    "  if ($slt.ref.bool($0.ref, n)) {\n"
    "    p := $CurrAddr;\n"
    "    havoc $CurrAddr;\n"
    "    assume $sge.ref.bool($sub.ref($CurrAddr, n), p);\n"
    "    assume $sgt.ref.bool($CurrAddr, $0.ref) && $slt.ref.bool($CurrAddr, $MALLOC_TOP);\n"
    "    assume $Size(p) == n;\n"
    "    assume (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);\n"
    "    $Alloc[p] := true;\n"
    "  } else {\n"
    "    p := $0.ref;\n"
    "  }\n"
    "}\n");

  D("procedure $free(p: ref)\n"
    "modifies $Alloc, $allocatedCounter;\n"
    "{\n"
    "  if ($ne.ref.bool(p, $0.ref)) {\n"
    "    assert {:valid_free} $eq.ref.bool($base(p), p);\n"
    "    assert {:valid_free} $Alloc[p];\n"
    "    assert {:valid_free} $slt.ref.bool($0.ref, p);\n"
    "    $Alloc[p] := false;\n"
    "    $allocatedCounter := $allocatedCounter - 1;\n"
    "  }\n"
    "}\n");

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
  D("var $Alloc: [ref] bool;");
  D("var $Size: [ref] ref;\n");

  D("procedure $galloc(base_addr: ref, size: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $Size[base_addr] == size;\n"
    "ensures (forall addr: ref :: {$base(addr)} $sle.ref.bool(base_addr, addr) && $slt.ref.bool(addr, $add.ref(base_addr, size)) ==> $base(addr) == base_addr);\n"
    "ensures $Alloc[base_addr];\n"
    "ensures (forall q: ref :: {$Size[q]} q != base_addr ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != base_addr ==> $Alloc[q] == old($Alloc[q]));\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $sle.ref.bool($0.ref, n);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $slt.ref.bool($0.ref, p) && $slt.ref.bool(p, $sub.ref($MALLOC_TOP, n));\n"
    "ensures $eq.ref.bool(n, $0.ref) ==> p == $0.ref;\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: ref :: old($Alloc[q]) ==> ($slt.ref.bool($add.ref(p, n), q) || $slt.ref.bool($add.ref(q, $Size[q]), p)));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);\n");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc, $allocatedCounter;\n"
    "requires $eq.ref.bool(p, $0.ref) || ($eq.ref.bool($base(p), p) && $Alloc[p]);\n"
    "requires $slt.ref.bool($0.ref, p);\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> !$Alloc[p];\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> $allocatedCounter == old($allocatedCounter) - 1;\n");

#else // NO_REUSE does not reuse previously-allocated addresses
  D("var $Alloc: [ref] bool;");
  D("function $Size(ref) returns (ref);");
  D("var $CurrAddr:ref;\n");

  D("procedure $galloc(base_addr: ref, size: ref);\n"
    "modifies $Alloc;\n"
    "ensures $Size(base_addr) == size;\n"
    "ensures (forall addr: ref :: {$base(addr)} $sle.ref.bool(base_addr, addr) && $slt.ref.bool(addr, $add.ref(base_addr, size)) ==> $base(addr) == base_addr);\n"
    "ensures $Alloc[base_addr];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != base_addr ==> $Alloc[q] == old($Alloc[q]));\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $Alloc, $CurrAddr;\n"
    "ensures $sle.ref.bool($0.ref, n);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $sge.ref.bool($sub.ref($CurrAddr, n), old($CurrAddr)) && p == old($CurrAddr);\n"
    "ensures $sgt.ref.bool($CurrAddr, $0.ref) && $slt.ref.bool($CurrAddr, $MALLOC_TOP);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $Size(p) == n;\n"
    "ensures $slt.ref.bool($0.ref, n) ==> (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $Alloc[p];\n"
    "ensures $eq.ref.bool(n, $0.ref) ==> old($CurrAddr) == $CurrAddr && p == $0.ref;\n"
    "ensures $eq.ref.bool(n, $0.ref)==> $Alloc[p] == old($Alloc)[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc, $allocatedCounter;\n"
    "requires $eq.ref.bool(p, $0.ref) || ($eq.ref.bool($base(p), p) && $Alloc[p]);\n"
    "requires $slt.ref.bool($0.ref, p);\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> !$Alloc[p];\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> $allocatedCounter == old($allocatedCounter) - 1;\n");
#endif

#else
  D("procedure $malloc(n: ref) returns (p: ref)\n"
    "{\n"
    "  call p := $$alloc(n);\n"
    "}\n");

#if MEMORY_MODEL_NO_REUSE_IMPLS
  D("var $CurrAddr:ref;\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref)\n"
    "modifies $CurrAddr;\n"
    "{\n"
    "  assume $sge.ref.bool(n, $0.ref);\n"
    "  if ($sgt.ref.bool(n, $0.ref)) {\n"
    "    p := $CurrAddr;\n"
    "    havoc $CurrAddr;\n"
    "    assume $sge.ref.bool($sub.ref($CurrAddr, n), p);\n"
    "    assume $sgt.ref.bool($CurrAddr, $0.ref) && $slt.ref.bool($CurrAddr, $MALLOC_TOP);\n"
    "  } else {\n"
    "    p := $0.ref;\n"
    "  }\n"
    "}\n");

  D("procedure $free(p: ref);\n");

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
  D("var $Alloc: [ref] bool;");
  D("var $Size: [ref] ref;\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $sle.ref.bool($0.ref, n);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $slt.ref.bool($0.ref, p) && $slt.ref.bool(p, $sub.ref($MALLOC_TOP, n));\n"
    "ensures $eq.ref.bool(n, $0.ref) ==> p == $0.ref;\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: ref :: old($Alloc[q]) ==> ($slt.ref.bool($add.ref(p, n), q) || $slt.ref.bool($add.ref(q, $Size[q]), p)));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc;\n"
    "ensures !$Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n");

#else // NO_REUSE does not reuse previously-allocated addresses
  D("var $CurrAddr:ref;\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $CurrAddr;\n"
    "ensures $sle.ref.bool($0.ref, n);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $sge.ref.bool($sub.ref($CurrAddr, n), old($CurrAddr)) && p == old($CurrAddr);\n"
    "ensures $sgt.ref.bool($CurrAddr, $0.ref) && $slt.ref.bool($CurrAddr, $MALLOC_TOP);\n"
    "ensures $eq.ref.bool(n, $0.ref) ==> old($CurrAddr) == $CurrAddr && p == $0.ref;\n");

  D("procedure $free(p: ref);\n");
#endif
#endif

#undef D
}

#if MEMORY_SAFETY
// The size parameter represents number of bytes that are being accessed
void __SMACK_check_memory_safety(void* pointer, unsigned long size) {
  void* sizeRef = (void*)size;
  __SMACK_code("assert {:valid_deref} $Alloc[$base(@)];", pointer);
  __SMACK_code("assert {:valid_deref} $sle.ref.bool($base(@), @);", pointer, pointer);
#if MEMORY_MODEL_NO_REUSE_IMPLS
  __SMACK_code("assert {:valid_deref} $sle.ref.bool($add.ref(@, @), $add.ref($base(@), $Size($base(@))));", pointer, sizeRef, pointer, pointer);
#elif MEMORY_MODEL_REUSE
  __SMACK_code("assert {:valid_deref} $sle.ref.bool($add.ref(@, @), $add.ref($base(@), $Size[$base(@)]));", pointer, sizeRef, pointer, pointer);
#else
  __SMACK_code("assert {:valid_deref} $sle.ref.bool($add.ref(@, @), $add.ref($base(@), $Size($base(@))));", pointer, sizeRef, pointer, pointer);
#endif
}

void __SMACK_check_memory_leak(void) {
  __SMACK_code("assert {:valid_memtrack} $allocatedCounter == 0;");
}
#endif

void __SMACK_init_func_memory_model(void) {
#if MEMORY_MODEL_NO_REUSE || MEMORY_MODEL_NO_REUSE_IMPLS
  __SMACK_code("$CurrAddr := $1024.ref;");
#endif
#if MEMORY_SAFETY
  __SMACK_code("$allocatedCounter := 0;");
#endif
}
