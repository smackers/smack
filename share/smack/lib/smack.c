//
// This file is distributed under the MIT License. See LICENSE for details.

#include <smack.h>
#include <limits.h>
#include <string.h>
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

#if SIGNED_INTEGER_OVERFLOW_CHECK
void __SMACK_overflow_false(void) {
  __SMACK_code("assert {:overflow} false;");
}

void __SMACK_check_overflow(int flag) {
  __SMACK_dummy(flag); __SMACK_code("assert {:overflow} @ == $0;", flag);
}
#endif

void exit(int x) {
#if MEMORY_SAFETY
  __SMACK_code("assert $allocatedCounter == 0;");
#endif
  __SMACK_code("assume false;");
  while(1);
}

char __VERIFIER_nondet_char() {
  char x = __SMACK_nondet_char();
  __VERIFIER_assume(x >= SCHAR_MIN && x <= SCHAR_MAX);
  return x;
}

signed char __VERIFIER_nondet_signed_char() {
  signed char x = __SMACK_nondet_signed_char();
  __VERIFIER_assume(x >= SCHAR_MIN && x <= SCHAR_MAX);
  return x;
}

unsigned char __VERIFIER_nondet_unsigned_char() {
  unsigned char x = __SMACK_nondet_unsigned_char();
  __VERIFIER_assume(x >= 0 && x <= UCHAR_MAX);
  return x;
}

short __VERIFIER_nondet_short() {
  short x = __SMACK_nondet_short();
  __VERIFIER_assume(x >= SHRT_MIN && x <= SHRT_MAX);
  return x;
}

signed short __VERIFIER_nondet_signed_short() {
  signed short x = __SMACK_nondet_signed_short();
  __VERIFIER_assume(x >= SHRT_MIN && x <= SHRT_MAX);
  return x;
}

signed short int __VERIFIER_nondet_signed_short_int() {
  signed short int x = __SMACK_nondet_signed_short_int();
  __VERIFIER_assume(x >= SHRT_MIN && x <= SHRT_MAX);
  return x;
}

unsigned short __VERIFIER_nondet_unsigned_short() {
  unsigned short x = __SMACK_nondet_unsigned_short();
  __VERIFIER_assume(x >= 0 && x <= USHRT_MAX);
  return x;
}

unsigned short int __VERIFIER_nondet_unsigned_short_int() {
  unsigned short int x = __SMACK_nondet_unsigned_short_int();
  __VERIFIER_assume(x >= 0 && x <= USHRT_MAX);
  return x;
}

int __VERIFIER_nondet_int() {
  int x = __SMACK_nondet_int();
  __VERIFIER_assume(x >= INT_MIN && x <= INT_MAX);
  return x;
}

signed int __VERIFIER_nondet_signed_int() {
  signed int x = __SMACK_nondet_signed_int();
  __VERIFIER_assume(x >= INT_MIN && x <= INT_MAX);
  return x;
}

unsigned __VERIFIER_nondet_unsigned() {
  unsigned x = __SMACK_nondet_unsigned();
  __VERIFIER_assume(x >= 0 && x <= UINT_MAX);
  return x;
}

unsigned int __VERIFIER_nondet_unsigned_int() {
  unsigned int x = __SMACK_nondet_unsigned_int();
  __VERIFIER_assume(x >= 0 && x <= UINT_MAX);
  return x;
}

long __VERIFIER_nondet_long() {
  long x = __SMACK_nondet_long();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

long int __VERIFIER_nondet_long_int() {
  long int x = __SMACK_nondet_long_int();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

signed long __VERIFIER_nondet_signed_long() {
  signed long x = __SMACK_nondet_signed_long();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

signed long int __VERIFIER_nondet_signed_long_int() {
  signed long int x = __SMACK_nondet_signed_long_int();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

unsigned long __VERIFIER_nondet_unsigned_long() {
  unsigned long x = __SMACK_nondet_unsigned_long();
  __VERIFIER_assume(x >= 0 && x <= ULONG_MAX);
  return x;
}

unsigned long int __VERIFIER_nondet_unsigned_long_int() {
  unsigned long int x = __SMACK_nondet_unsigned_long_int();
  __VERIFIER_assume(x >= 0 && x <= ULONG_MAX);
  return x;
}

long long __VERIFIER_nondet_long_long() {
  long long x = __SMACK_nondet_long_long();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

long long int __VERIFIER_nondet_long_long_int() {
  long long int x = __SMACK_nondet_long_long_int();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

signed long long __VERIFIER_nondet_signed_long_long() {
  signed long long x = __SMACK_nondet_signed_long_long();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

signed long long int __VERIFIER_nondet_signed_long_long_int() {
  signed long long int x = __SMACK_nondet_signed_long_long_int();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

unsigned long long __VERIFIER_nondet_unsigned_long_long() {
  unsigned long long x = __SMACK_nondet_unsigned_long_long();
  __VERIFIER_assume(x >= 0 && x <= ULLONG_MAX);
  return x;
}

unsigned long long int __VERIFIER_nondet_unsigned_long_long_int() {
  unsigned long long int x = __SMACK_nondet_unsigned_long_long_int();
  __VERIFIER_assume(x >= 0 && x <= ULLONG_MAX);
  return x;
}

// Apparently used in SVCCOMP benchmarks
_Bool __VERIFIER_nondet_bool(void) {
  _Bool x = (_Bool)__VERIFIER_nondet_int();
  __VERIFIER_assume(x == 0 || x == 1);
  return x;
}

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

#if FLOAT_ENABLED

  //Check the length of pointers
  //#if ( __WORDSIZE == 64 )
  #if defined(__LP64__) || defined(_LP64)
  #define BUILD_64   1
  #endif

float fabsf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $abs.bvfloat(@);", ret, x);
  return ret;
}

float fdimf(float x, float y) {
  if(x>y)
    return x-y;
  else
    return 0;
}

float roundf(float x) {
  if (__isnan(x) || __isinf(x) || __iszero(x))
    return x;
  double rete = __VERIFIER_nondet_double();
  double reta = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv32td($round.rne.bvfloat(@));", rete, x);
  __SMACK_code("@ := sbv32td($round.rna.bvfloat(@));", reta, x);
  if (x > 0)
    return fmax(rete, reta);
  return fmin(rete, reta);
}

long lroundf(float x) {
  long ret = __VERIFIER_nondet_long();
  __SMACK_code("@ := $lround.bvfloat(dtf(@));", ret, x);
  return ret;
}

float rintf(float x) {
  return roundf(x);
}

float nearbyintf(float x) {
  return roundf(x);
}

long lrintf(float x) {
  long ret = __VERIFIER_nondet_long();
  __SMACK_code("@ := $lround.bvfloat(dtf(@));", ret, x);
  return ret;
}

float floorf(float x) {
  if (__isnanf(x) || __isinff(x) || __iszerof(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv32td($floor.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float ceilf(float x) {
  if (__isnanf(x) || __isinff(x) || __iszerof(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv32td($ceil.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float truncf(float x) {
  if (__isnanf(x) || __isinff(x) || __iszerof(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv32td($trunc.bvfloat(dtf(@)));", ret, x);
  return ret;
}

float sqrtf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $sqrt.bvfloat(dtf(@));", ret, x);
  return ret;
}

float remainderf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rem.bvfloat(dtf(@), dtf(@)));", ret, x, y);
  return ret;
}

float fminf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $min.bvfloat(dtf(@), dtf(@));", ret, x, y);
  return ret;
}

float fmaxf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $max.bvfloat(dtf(@), dtf(@));", ret, x, y);
  return ret;
}

float fmodf(float x, float y) {
  float result = remainderf(fabsf(x), fabsf(y));
  if (signbitf(result)) 
    result += fabsf(y);
  return copysignf(result, x);
}

float modff(float x, float* y) {
  *y = floorf(x);
  return x -*y;
}

float copysignf(float x, float y) {
  double ret = __VERIFIER_nondet_double();
  if (__isnegativef(x)^__isnegativef(y))
    __SMACK_code("@ := $fmul.bvfloat(dtf(@), -0e127f24e8);", ret, x);
  else
    ret = x;
  return ret;
}

int __isnormalf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isSubnormalf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __iszerof(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}
  
int __isinff(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}
  
int __isnanf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isnegativef(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnegative.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __ispositivef(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $ispositive.bvfloat(dtf(@)) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __signbitf(float x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if (dtf(@) <= 0e0f24e8) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int signbitf(float x) {
  return __signbitf(x);
}

int __fpclassifyf(float x) {
  if (__isnanf(x))
    return 0;
  if (__isinff(x))
    return 1;
  if (__iszerof(x))
    return 2;
  if (__isSubnormalf(x))
    return 3;
  return 4;
}

int fpclassifyf(float x) {
  return __fpclassifyf(x);
}

int __finitef(float x) {
  return !__isinf(x) && !__isnanf(x);
}

double fabs(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $abs.bvdouble(@);", ret, x);
  return ret;
}

double fdim(double x, double y) {
  if(x>y)
    return x-y;
  else
    return 0;
}

double round(double x) {
  if (__isnan(x) || __isinf(x) || __iszero(x))
    return x;
  double rete = __VERIFIER_nondet_double();
  double reta = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv64td($round.rne.bvdouble(@));", rete, x);
  __SMACK_code("@ := sbv64td($round.rna.bvdouble(@));", reta, x);
  if (x > 0)
    return fmax(rete, reta);
  return fmin(rete, reta);
}

long lround(double x) {
  long ret = __VERIFIER_nondet_long();
  __SMACK_code("@ := $lround.bvdouble(@);", ret, x);
  return ret;
}

double rint(double x) {
  return round(x);
}

double nearbyint(double x) {
  return round(x);
}

long lrint(double x) {
  return lround(x);
}

double floor(double x) {
  if (__isnan(x) || __isinf(x) || __iszero(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv64td($floor.bvdouble(@));", ret, x);
  return ret;
}

double ceil(double x) {
  if (__isnan(x) || __isinf(x) || __iszero(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv64td($ceil.bvdouble(@));", ret, x);
  return ret;
}

double trunc(double x) {
  if (__isnan(x) || __isinf(x) || __iszero(x))
    return x;
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := sbv64td($trunc.bvdouble(@));", ret, x);
  return ret;
}

double sqrt(double x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $sqrt.bvdouble(@);", ret, x);
  return ret;
}

double remainder(double x, double y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd(dtf($rem.bvdouble(ftd(dtf(@)), ftd(dtf(@)))));", ret, x, y);
  return ret;
}

double fmin(double x, double y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $min.bvdouble(@, @);", ret, x, y);
  return ret;
}

double fmax(double x, double y) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $max.bvdouble(@, @);", ret, x, y);
  return ret;
}

double fmod(double x, double y) {
  double result = remainder(fabs(x), fabs(y));
  if (signbit(result))
    result += fabs(y);
  return copysign(result, x);
}

double modf(double x, double* y) {
  *y = floor(x);
  return x - *y;
}

double copysign(double x, double y) {
  double ret = __VERIFIER_nondet_double();
  if (__isnegative(x)^__isnegative(y))
    __SMACK_code("@ := $fmul.bvdouble(@, -0e1023f53e11);", ret, x);
  else
    ret = x;
  return ret;
}

double nan(const char* x) {
  return 0.0/0.0;
}

int __isnormal(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isSubnormal(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __iszero(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}
  
int __isinf(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}
  
int __isnan(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isnegative(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnegative.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __ispositive(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $ispositive.bvdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __signbit(double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if (@ <= 0e0f53e11) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int signbit(double x) {
  return __signbit(x);
}

int __fpclassify(double x) {
  if (__isnan(x))
    return 0;
  if (__isinf(x))
    return 1;
  if (__iszero(x))
    return 2;
  if (__isSubnormal(x))
    return 3;
  return 4;
}

int fpclassify(double x) {
  return __fpclassify(x);
}

int __finite(double x) {
  return !__isinf(x) && !__isnan(x);
}

/*int __isnormall(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnormal.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isSubnormall(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $issubnormal.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __iszerol(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $iszero.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}
  
int __isinfl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isinfinite.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}
  
int __isnanl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnan.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __isnegativel(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $isnegative.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __ispositivel(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if $ispositive.bvlongdouble(@) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int __signbitl(long double x) {
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("@ := if (@ <= 0e0f53e11) then 1bv32 else 0bv32;", ret, x);
  return ret;
}

int signbitl(long double x) {
  return __signbitl(x);
}

int __fpclassifyl(long double x) {
  if (__isnanl(x))
    return 0;
  if (__isinfl(x))
    return 1;
  if (__iszerol(x))
    return 2;
  if (__isSubnormall(x))
    return 3;
  return 4;
}

int fpclassifyl(long double x) {
  return __fpclassifyl(x);
}

int __finitel(long double x) {
  return !__isinfl(x) && !__isnanl(x);
}*/
#endif

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

#define FPBUILTIN_UNARY_OP(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type(f: type) returns (type);

#define FPBUILTIN_BINARY_OP(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type(f1: type, f2: type) returns (type);

#define FPBUILTIN_BINARY_PRED(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type(f1: type, f2: type) returns (i1);

#define INLINE_FPBUILTIN_BINARY_PRED(type,name,prim) \
  function {:bvbuiltin xstr(prim)} name.type.bool(f1: type, f2: type) returns (bool); \
  function {:inline} name.type(f1: type, f2: type) returns (bv1) {if name.type.bool(f1,f2) then 1bv1 else 0bv1}

#define INLINE_FPBUILTIN_BINARY_SELECT(type,name,pred) \
  function {:inline} name.type(f1: type, f2: type) returns (type) {if pred.type.bool(f1,f2) then i1 else i2}

#define D(d) __SMACK_top_decl(d)

#define DECLARE(M,args...) \
  D(xstr(M(args)))

#define DECLARE_EACH_INT_TYPE(M,args...) \
  D(xstr(M(i128,args))); \
  D(xstr(M(i96,args))); \
  D(xstr(M(i88,args))); \
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
  D(xstr(M(bv88,args))); \
  D(xstr(M(bv64,args))); \
  D(xstr(M(bv56,args))); \
  D(xstr(M(bv48,args))); \
  D(xstr(M(bv40,args))); \
  D(xstr(M(bv32,args))); \
  D(xstr(M(bv24,args))); \
  D(xstr(M(bv16,args))); \
  D(xstr(M(bv8,args))); \
  D(xstr(M(bv1,args)));

#define DECLARE_EACH_FLOAT_TYPE(M,args...) \
  D(xstr(M(bvfloat,args))); \
  D(xstr(M(bvdouble,args))); \
  D(xstr(M(bvlongdouble,args)));

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
  DECLARE(INLINE_CONVERSION,bv128,bv88,$trunc,{i[88:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv64,$trunc,{i[64:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv56,$trunc,{i[56:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv48,$trunc,{i[48:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv40,$trunc,{i[40:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv32,$trunc,{i[32:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv24,$trunc,{i[24:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv128,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv88,$trunc,{i[88:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv64,$trunc,{i[64:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv56,$trunc,{i[56:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv48,$trunc,{i[48:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv40,$trunc,{i[40:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv32,$trunc,{i[32:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv24,$trunc,{i[24:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv96,bv1,$trunc,{i[1:0]});
  DECLARE(INLINE_CONVERSION,bv88,bv64,$trunc,{i[64:0]});
  DECLARE(INLINE_CONVERSION,bv88,bv56,$trunc,{i[56:0]});
  DECLARE(INLINE_CONVERSION,bv88,bv48,$trunc,{i[48:0]});
  DECLARE(INLINE_CONVERSION,bv88,bv40,$trunc,{i[40:0]});
  DECLARE(INLINE_CONVERSION,bv88,bv32,$trunc,{i[32:0]});
  DECLARE(INLINE_CONVERSION,bv88,bv24,$trunc,{i[24:0]});
  DECLARE(INLINE_CONVERSION,bv88,bv16,$trunc,{i[16:0]});
  DECLARE(INLINE_CONVERSION,bv88,bv8,$trunc,{i[8:0]});
  DECLARE(INLINE_CONVERSION,bv88,bv1,$trunc,{i[1:0]});
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
  D("axiom($and.i32(32, 16) == 0);");

  DECLARE(INLINE_CONVERSION,i128,i96,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i128,i88,$trunc,{i});
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
  DECLARE(INLINE_CONVERSION,i96,i88,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i56,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i48,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i40,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i32,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i24,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i96,i1,$trunc,{i});

  DECLARE(INLINE_CONVERSION,i88,i64,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i88,i88,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i88,i56,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i88,i48,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i88,i40,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i88,i32,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i88,i24,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i88,i16,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i88,i8,$trunc,{i});
  DECLARE(INLINE_CONVERSION,i88,i1,$trunc,{i});

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
  DECLARE(INLINE_CONVERSION,i1,i88,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i1,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i16,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i24,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i32,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i40,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i88,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i8,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i24,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i32,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i40,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i88,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i16,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i32,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i40,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i88,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i24,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i40,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i88,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i32,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i48,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i88,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i40,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i48,i56,$zext,{i});
  DECLARE(INLINE_CONVERSION,i48,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i48,i88,$zext,{i});
  DECLARE(INLINE_CONVERSION,i48,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i48,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i56,i64,$zext,{i});
  DECLARE(INLINE_CONVERSION,i56,i88,$zext,{i});
  DECLARE(INLINE_CONVERSION,i56,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i56,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i64,i88,$zext,{i});
  DECLARE(INLINE_CONVERSION,i64,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i64,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i88,i96,$zext,{i});
  DECLARE(INLINE_CONVERSION,i88,i128,$zext,{i});
  DECLARE(INLINE_CONVERSION,i96,i128,$zext,{i});

  DECLARE(INLINE_CONVERSION,i1,i8,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i16,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i24,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i40,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i88,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i1,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i16,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i24,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i40,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i88,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i8,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i24,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i40,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i88,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i16,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i32,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i40,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i88,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i24,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i40,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i88,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i32,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i48,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i88,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i40,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i48,i56,$sext,{i});
  DECLARE(INLINE_CONVERSION,i48,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i48,i88,$sext,{i});
  DECLARE(INLINE_CONVERSION,i48,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i48,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i56,i64,$sext,{i});
  DECLARE(INLINE_CONVERSION,i56,i88,$sext,{i});
  DECLARE(INLINE_CONVERSION,i56,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i56,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i64,i88,$sext,{i});
  DECLARE(INLINE_CONVERSION,i64,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i64,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i88,i96,$sext,{i});
  DECLARE(INLINE_CONVERSION,i88,i128,$sext,{i});
  DECLARE(INLINE_CONVERSION,i96,i128,$sext,{i});

  //Non bit-precise modeling of floating-points

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
  D("function $fp2si.float.i88(f:float) returns (i88);");
  D("function $fp2ui.float.i88(f:float) returns (i88);");
  D("function $si2fp.i88.float(i:i88) returns (float);");
  D("function $ui2fp.i88.float(i:i88) returns (float);");
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
  D("function $fp2si.float.bv88(f:float) returns (bv88);");
  D("function $fp2ui.float.bv88(f:float) returns (bv88);");
  D("function $si2fp.bv88.float(i:bv88) returns (float);");
  D("function $ui2fp.bv88.float(i:bv88) returns (float);");
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
  D("axiom (forall i: i88 :: $fp2ui.float.i88($ui2fp.i88.float(i)) == i);");
  D("axiom (forall f: float :: $ui2fp.i88.float($fp2ui.float.i88(f)) == f);");
  D("axiom (forall i: i88 :: $fp2si.float.i88($si2fp.i88.float(i)) == i);");
  D("axiom (forall f: float :: $si2fp.i88.float($fp2si.float.i88(f)) == f);");
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

#if FLOAT_ENABLED
  // Bit-precise modeling of floating-points

  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_OP, $fadd, {i1 + i2})
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_OP, $fsub, {i1 - i2})
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_OP, $fmul, {i1 * i2})
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_OP, $fdiv, {i1 / i2})
  DECLARE_EACH_FLOAT_TYPE(FPBUILTIN_BINARY_OP, $frem, fp.rem)
  D("function $ffalse.bvfloat(f1:bvfloat, f2:bvfloat) returns (i1);");
  D("function $ftrue.bvfloat(f1:bvfloat, f2:bvfloat) returns (i1);");
  
  D("function {:builtin \"fp.abs\"} $abs.bvfloat(bvfloat) returns (bvfloat);");
  D("function {:builtin \"fp.fma\"} $fma.bvfloat(bvfloat, bvfloat, bvfloat) returns (bvfloat);");
  D("function {:builtin \"fp.sqrt\"} $sqrt.bvfloat(bvfloat) returns (bvfloat);");
  D("function {:builtin \"fp.rem\"} $rem.bvfloat(bvfloat, bvfloat) returns (bvfloat);");
  D("function {:builtin \"fp.min\"} $min.bvfloat(bvfloat, bvfloat) returns (bvfloat);");
  D("function {:builtin \"fp.max\"} $max.bvfloat(bvfloat, bvfloat) returns (bvfloat);");
  
  D("function {:builtin \"fp.abs\"} $abs.bvdouble(bvdouble) returns (bvdouble);");
  D("function {:builtin \"fp.fma\"} $fma.bvdouble(bvdouble, bvdouble, bvdouble) returns (bvdouble);");
  D("function {:builtin \"fp.sqrt\"} $sqrt.bvdouble(bvdouble) returns (bvdouble);");
  D("function {:builtin \"fp.rem\"} $rem.bvdouble(bvdouble, bvdouble) returns (bvdouble);");
  D("function {:builtin \"fp.min\"} $min.bvdouble(bvdouble, bvdouble) returns (bvdouble);");
  D("function {:builtin \"fp.max\"} $max.bvdouble(bvdouble, bvdouble) returns (bvdouble);");
  
  D("function {:builtin \"fp.isNormal\"} $isnormal.bvfloat(bvfloat) returns (bool);");
  D("function {:builtin \"fp.isSubnormal\"} $issubnormal.bvfloat(bvfloat) returns (bool);");
  D("function {:builtin \"fp.isZero\"} $iszero.bvfloat(bvfloat) returns (bool);");
  D("function {:builtin \"fp.isInfinite\"} $isinfinite.bvfloat(bvfloat) returns (bool);");
  D("function {:builtin \"fp.isNaN\"} $isnan.bvfloat(bvfloat) returns (bool);");
  D("function {:builtin \"fp.isNegative\"} $isnegative.bvfloat(bvfloat) returns (bool);");
  D("function {:builtin \"fp.isPositive\"} $ispositive.bvfloat(bvfloat) returns (bool);");

  D("function {:builtin \"fp.isNormal\"} $isnormal.bvdouble(bvdouble) returns (bool);");
  D("function {:builtin \"fp.isSubnormal\"} $issubnormal.bvdouble(bvdouble) returns (bool);");
  D("function {:builtin \"fp.isZero\"} $iszero.bvdouble(bvdouble) returns (bool);");
  D("function {:builtin \"fp.isInfinite\"} $isinfinite.bvdouble(bvdouble) returns (bool);");
  D("function {:builtin \"fp.isNaN\"} $isnan.bvdouble(bvdouble) returns (bool);");
  D("function {:builtin \"fp.isNegative\"} $isnegative.bvdouble(bvdouble) returns (bool);");
  D("function {:builtin \"fp.isPositive\"} $ispositive.bvdouble(bvdouble) returns (bool);");
  
  D("function {:builtin \"fp.isNormal\"} $isnormal.bvlongdouble(bvlongdouble) returns (bool);");
  D("function {:builtin \"fp.isSubnormal\"} $issubnormal.bvlongdouble(bvlongdouble) returns (bool);");
  D("function {:builtin \"fp.isZero\"} $iszero.bvlongdouble(bvlongdouble) returns (bool);");
  D("function {:builtin \"fp.isInfinite\"} $isinfinite.bvlongdouble(bvlongdouble) returns (bool);");
  D("function {:builtin \"fp.isNaN\"} $isnan.bvlongdouble(bvlongdouble) returns (bool);");
  D("function {:builtin \"fp.isNegative\"} $isnegative.bvlongdouble(bvlongdouble) returns (bool);");
  D("function {:builtin \"fp.isPositive\"} $ispositive.bvlongdouble(bvlongdouble) returns (bool);");

  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $foeq, i1 == i2)
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $fone, !(i1 == i2))
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $fole, i1 <= i2)
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $folt, i1 < i2)
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $foge, i1 >= i2)
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $fogt, i1 > i2)
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $fueq, i1 == i2)
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $fune, !(i1 == i2))
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $fule, i1 <= i2)
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $fult, i1 < i2)
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $fuge, i1 >= i2)
  DECLARE_EACH_FLOAT_TYPE(INLINE_BINARY_BV_PRED, $fugt, i1 > i2)

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

  //This isn't the correct implementation, so change as needed
  D("function {:inline} $ford.bvfloat(f1:bvfloat, f2:bvfloat) returns (bv1);");
  D("function {:inline} $funo.bvfloat(f1:bvfloat, f2:bvfloat) returns (bv1);");

  D("function $fptrunc.bvfloat.bvfloat(f:bvfloat) returns (bvfloat) {f}");
  D("function $fpext.bvfloat.bvfloat(f:bvfloat) returns (bvfloat) {f}");

  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv128tf(bv128) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv96tf(bv96) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv88tf(bv88) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv64tf(bv64) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv56tf(bv56) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv48tf(bv48) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv40tf(bv40) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv32tf(bv32) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv24tf(bv24) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv16tf(bv16) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} sbv8tf(bv8) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv128tf(bv128) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv96tf(bv96) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv88tf(bv88) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv64tf(bv64) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv56tf(bv56) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv48tf(bv48) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv40tf(bv40) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv32tf(bv32) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv24tf(bv24) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv16tf(bv16) returns (bvfloat);");
  D("function {:builtin \"(_ to_fp 8 24) RNE\"} ubv8tf(bv8) returns (bvfloat);");
  D("function {:builtin \"(_ fp.to_sbv 128) RNE\"} ftsbv128(bvfloat) returns (bv128);");
  D("function {:builtin \"(_ fp.to_sbv 96) RNE\"} ftsbv96(bvfloat) returns (bv96);");
  D("function {:builtin \"(_ fp.to_sbv 88) RNE\"} ftsbv88(bvfloat) returns (bv88);");
  D("function {:builtin \"(_ fp.to_sbv 64) RNE\"} ftsbv64(bvfloat) returns (bv64);");
  D("function {:builtin \"(_ fp.to_sbv 56) RNE\"} ftsbv56(bvfloat) returns (bv56);");
  D("function {:builtin \"(_ fp.to_sbv 48) RNE\"} ftsbv48(bvfloat) returns (bv48);");
  D("function {:builtin \"(_ fp.to_sbv 40) RNE\"} ftsbv40(bvfloat) returns (bv40);");
  D("function {:builtin \"(_ fp.to_sbv 32) RNE\"} ftsbv32(bvfloat) returns (bv32);");
  D("function {:builtin \"(_ fp.to_sbv 24) RNE\"} ftsbv24(bvfloat) returns (bv24);");
  D("function {:builtin \"(_ fp.to_sbv 16) RNE\"} ftsbv16(bvfloat) returns (bv16);");
  D("function {:builtin \"(_ fp.to_sbv 8) RNE\"} ftsbv8(bvfloat) returns (bv8);");
  D("function {:builtin \"(_ fp.to_ubv 128) RNE\"} ftubv128(bvfloat) returns (bv128);");
  D("function {:builtin \"(_ fp.to_ubv 96) RNE\"} ftubv96(bvfloat) returns (bv96);");
  D("function {:builtin \"(_ fp.to_ubv 88) RNE\"} ftubv88(bvfloat) returns (bv88);");
  D("function {:builtin \"(_ fp.to_ubv 64) RNE\"} ftubv64(bvfloat) returns (bv64);");
  D("function {:builtin \"(_ fp.to_ubv 56) RNE\"} ftubv56(bvfloat) returns (bv56);");
  D("function {:builtin \"(_ fp.to_ubv 48) RNE\"} ftubv48(bvfloat) returns (bv48);");
  D("function {:builtin \"(_ fp.to_ubv 40) RNE\"} ftubv40(bvfloat) returns (bv40);");
  D("function {:builtin \"(_ fp.to_ubv 32) RNE\"} ftubv32(bvfloat) returns (bv32);");
  D("function {:builtin \"(_ fp.to_ubv 24) RNE\"} ftubv24(bvfloat) returns (bv24);");
  D("function {:builtin \"(_ fp.to_ubv 16) RNE\"} ftubv16(bvfloat) returns (bv16);");
  D("function {:builtin \"(_ fp.to_ubv 8) RNE\"} ftubv8(bvfloat) returns (bv8);");
  
  // Add truncation for default casts to int
  D("function {:builtin \"(_ fp.to_sbv 128) RTZ\"} ftsi128(bvfloat) returns (bv128);");
  D("function {:builtin \"(_ fp.to_sbv 96) RTZ\"} ftsi96(bvfloat) returns (bv96);");
  D("function {:builtin \"(_ fp.to_sbv 88) RTZ\"} ftsi88(bvfloat) returns (bv88);");
  D("function {:builtin \"(_ fp.to_sbv 64) RTZ\"} ftsi64(bvfloat) returns (bv64);");
  D("function {:builtin \"(_ fp.to_sbv 56) RTZ\"} ftsi56(bvfloat) returns (bv56);");
  D("function {:builtin \"(_ fp.to_sbv 48) RTZ\"} ftsi48(bvfloat) returns (bv48);");
  D("function {:builtin \"(_ fp.to_sbv 40) RTZ\"} ftsi40(bvfloat) returns (bv40);");
  D("function {:builtin \"(_ fp.to_sbv 32) RTZ\"} ftsi32(bvfloat) returns (bv32);");
  D("function {:builtin \"(_ fp.to_sbv 24) RTZ\"} ftsi24(bvfloat) returns (bv24);");
  D("function {:builtin \"(_ fp.to_sbv 16) RTZ\"} ftsi16(bvfloat) returns (bv16);");
  D("function {:builtin \"(_ fp.to_sbv 8) RTZ\"} ftsi8(bvfloat) returns (bv8);");
  
  DECLARE(INLINE_CONVERSION, bvfloat, bv128, $fp2si, {ftsi128(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv128, $fp2ui, {ftubv128(i)});
  DECLARE(INLINE_CONVERSION, bv128, bvfloat, $si2fp, {sbv128tf(i)});
  DECLARE(INLINE_CONVERSION, bv128, bvfloat, $ui2fp, {ubv128tf(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv96, $fp2si, {ftsi96(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv96, $fp2ui, {ftubv96(i)});
  DECLARE(INLINE_CONVERSION, bv96, bvfloat, $si2fp, {sbv96tf(i)});
  DECLARE(INLINE_CONVERSION, bv96, bvfloat, $ui2fp, {ubv96tf(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv88, $fp2si, {ftsi88(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv88, $fp2ui, {ftubv88(i)});
  DECLARE(INLINE_CONVERSION, bv88, bvfloat, $si2fp, {sbv88tf(i)});
  DECLARE(INLINE_CONVERSION, bv88, bvfloat, $ui2fp, {ubv88tf(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv64, $fp2si, {ftsi64(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv64, $fp2ui, {ftubv64(i)});
  DECLARE(INLINE_CONVERSION, bv64, bvfloat, $si2fp, {sbv64tf(i)});
  DECLARE(INLINE_CONVERSION, bv64, bvfloat, $ui2fp, {ubv64tf(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv56, $fp2si, {ftsi56(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv56, $fp2ui, {ftubv56(i)});
  DECLARE(INLINE_CONVERSION, bv56, bvfloat, $si2fp, {sbv56tf(i)});
  DECLARE(INLINE_CONVERSION, bv56, bvfloat, $ui2fp, {ubv56tf(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv48, $fp2si, {ftsi48(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv48, $fp2ui, {ftubv48(i)});
  DECLARE(INLINE_CONVERSION, bv48, bvfloat, $si2fp, {sbv48tf(i)});
  DECLARE(INLINE_CONVERSION, bv48, bvfloat, $ui2fp, {ubv48tf(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv40, $fp2si, {ftsi40(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv40, $fp2ui, {ftubv40(i)});
  DECLARE(INLINE_CONVERSION, bv40, bvfloat, $si2fp, {sbv40tf(i)});
  DECLARE(INLINE_CONVERSION, bv40, bvfloat, $ui2fp, {ubv40tf(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv32, $fp2si, {ftsi32(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv32, $fp2ui, {ftubv32(i)});
  DECLARE(INLINE_CONVERSION, bv32, bvfloat, $si2fp, {sbv32tf(i)});
  DECLARE(INLINE_CONVERSION, bv32, bvfloat, $ui2fp, {ubv32tf(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv24, $fp2si, {ftsi24(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv24, $fp2ui, {ftubv24(i)});
  DECLARE(INLINE_CONVERSION, bv24, bvfloat, $si2fp, {sbv24tf(i)});
  DECLARE(INLINE_CONVERSION, bv24, bvfloat, $ui2fp, {ubv24tf(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv16, $fp2si, {ftsi16(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv16, $fp2ui, {ftubv16(i)});
  DECLARE(INLINE_CONVERSION, bv16, bvfloat, $si2fp, {sbv16tf(i)});
  DECLARE(INLINE_CONVERSION, bv16, bvfloat, $ui2fp, {ubv16tf(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv8, $fp2si, {ftsi8(i)});
  DECLARE(INLINE_CONVERSION, bvfloat, bv8, $fp2ui, {ftubv8(i)});
  DECLARE(INLINE_CONVERSION, bv8, bvfloat, $si2fp, {sbv8tf(i)});
  DECLARE(INLINE_CONVERSION, bv8, bvfloat, $ui2fp, {ubv8tf(i)});
  
  D("function {:builtin \"(_ fp.to_sbv 32) RNE\"} $round.rne.bvfloat(bvfloat) returns (bv32);");
  D("function {:builtin \"(_ fp.to_sbv 32) RNA\"} $round.rna.bvfloat(bvfloat) returns (bv32);");
  D("function {:builtin \"(_ fp.to_sbv 32) RTN\"} $floor.bvfloat(bvfloat) returns (bv32);");
  D("function {:builtin \"(_ fp.to_sbv 32) RTP\"} $ceil.bvfloat(bvfloat) returns (bv32);");
  D("function {:builtin \"(_ fp.to_sbv 32) RTZ\"} $trunc.bvfloat(bvfloat) returns (bv32);");
  
  #if BUILD_64
    D("function {:builtin \"(_ fp.to_sbv 64) RNA\"} $lround.bvfloat(bvfloat) returns (bv64);");
  
  #else
    D("function {:builtin \"(_ fp.to_sbv 32) RNA\"} $lround.bvfloat(bvfloat) returns (bv32);");

  #endif
  
  //This isn't the correct implementation, so change as needed
  D("function {:inline} $ford.bvdouble(f1:bvdouble, f2:bvdouble) returns (bv1);");
  D("function {:inline} $funo.bvdouble(f1:bvdouble, f2:bvdouble) returns (bv1);");

  D("function $fptrunc.bvdouble.bvdouble(f:bvdouble) returns (bvdouble) {f}");
  D("function $fpext.bvdouble.bvdouble(f:bvdouble) returns (bvdouble) {f}");

  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv128td(bv128) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv96td(bv96) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv88td(bv88) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv64td(bv64) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv56td(bv56) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv48td(bv48) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv40td(bv40) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv32td(bv32) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv24td(bv24) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv16td(bv16) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} sbv8td(bv8) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv128td(bv128) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv96td(bv96) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv88td(bv88) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv64td(bv64) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv56td(bv56) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv48td(bv48) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv40td(bv40) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv32td(bv32) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv24td(bv24) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv16td(bv16) returns (bvdouble);");
  D("function {:builtin \"(_ to_fp 11 53) RNE\"} ubv8td(bv8) returns (bvdouble);");
  D("function {:builtin \"(_ fp.to_sbv 128) RNE\"} dtsbv128(bvdouble) returns (bv128);");
  D("function {:builtin \"(_ fp.to_sbv 96) RNE\"} dtsbv96(bvdouble) returns (bv96);");
  D("function {:builtin \"(_ fp.to_sbv 88) RNE\"} dtsbv88(bvdouble) returns (bv88);");
  D("function {:builtin \"(_ fp.to_sbv 64) RNE\"} dtsbv64(bvdouble) returns (bv64);");
  D("function {:builtin \"(_ fp.to_sbv 56) RNE\"} dtsbv56(bvdouble) returns (bv56);");
  D("function {:builtin \"(_ fp.to_sbv 48) RNE\"} dtsbv48(bvdouble) returns (bv48);");
  D("function {:builtin \"(_ fp.to_sbv 40) RNE\"} dtsbv40(bvdouble) returns (bv40);");
  D("function {:builtin \"(_ fp.to_sbv 32) RNE\"} dtsbv32(bvdouble) returns (bv32);");
  D("function {:builtin \"(_ fp.to_sbv 24) RNE\"} dtsbv24(bvdouble) returns (bv24);");
  D("function {:builtin \"(_ fp.to_sbv 16) RNE\"} dtsbv16(bvdouble) returns (bv16);");
  D("function {:builtin \"(_ fp.to_sbv 8) RNE\"} dtsbv8(bvdouble) returns (bv8);");
  D("function {:builtin \"(_ fp.to_ubv 128) RNE\"} dtubv128(bvdouble) returns (bv128);");
  D("function {:builtin \"(_ fp.to_ubv 96) RNE\"} dtubv96(bvdouble) returns (bv96);");
  D("function {:builtin \"(_ fp.to_ubv 88) RNE\"} dtubv88(bvdouble) returns (bv88);");
  D("function {:builtin \"(_ fp.to_ubv 64) RNE\"} dtubv64(bvdouble) returns (bv64);");
  D("function {:builtin \"(_ fp.to_ubv 56) RNE\"} dtubv56(bvdouble) returns (bv56);");
  D("function {:builtin \"(_ fp.to_ubv 48) RNE\"} dtubv48(bvdouble) returns (bv48);");
  D("function {:builtin \"(_ fp.to_ubv 40) RNE\"} dtubv40(bvdouble) returns (bv40);");
  D("function {:builtin \"(_ fp.to_ubv 32) RNE\"} dtubv32(bvdouble) returns (bv32);");
  D("function {:builtin \"(_ fp.to_ubv 24) RNE\"} dtubv24(bvdouble) returns (bv24);");
  D("function {:builtin \"(_ fp.to_ubv 16) RNE\"} dtubv16(bvdouble) returns (bv16);");
  D("function {:builtin \"(_ fp.to_ubv 8) RNE\"} dtubv8(bvdouble) returns (bv8);");
  
  // Add truncation for default casts to int
  D("function {:builtin \"(_ fp.to_sbv 128) RTZ\"} dtsi128(bvdouble) returns (bv128);");
  D("function {:builtin \"(_ fp.to_sbv 96) RTZ\"} dtsi96(bvdouble) returns (bv96);");
  D("function {:builtin \"(_ fp.to_sbv 88) RTZ\"} dtsi88(bvdouble) returns (bv88);");
  D("function {:builtin \"(_ fp.to_sbv 64) RTZ\"} dtsi64(bvdouble) returns (bv64);");
  D("function {:builtin \"(_ fp.to_sbv 56) RTZ\"} dtsi56(bvdouble) returns (bv56);");
  D("function {:builtin \"(_ fp.to_sbv 48) RTZ\"} dtsi48(bvdouble) returns (bv48);");
  D("function {:builtin \"(_ fp.to_sbv 40) RTZ\"} dtsi40(bvdouble) returns (bv40);");
  D("function {:builtin \"(_ fp.to_sbv 32) RTZ\"} dtsi32(bvdouble) returns (bv32);");
  D("function {:builtin \"(_ fp.to_sbv 24) RTZ\"} dtsi24(bvdouble) returns (bv24);");
  D("function {:builtin \"(_ fp.to_sbv 16) RTZ\"} dtsi16(bvdouble) returns (bv16);");
  D("function {:builtin \"(_ fp.to_sbv 8) RTZ\"} dtsi8(bvdouble) returns (bv8);");
  
  DECLARE(INLINE_CONVERSION, bvdouble, bv128, $fp2si, {dtsi128(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv128, $fp2ui, {dtubv128(i)});
  DECLARE(INLINE_CONVERSION, bv128, bvdouble, $si2fp, {sbv128td(i)});
  DECLARE(INLINE_CONVERSION, bv128, bvdouble, $ui2fp, {ubv128td(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv96, $fp2si, {dtsi96(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv96, $fp2ui, {dtubv96(i)});
  DECLARE(INLINE_CONVERSION, bv96, bvdouble, $si2fp, {sbv96td(i)});
  DECLARE(INLINE_CONVERSION, bv96, bvdouble, $ui2fp, {ubv96td(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv88, $fp2si, {dtsi88(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv88, $fp2ui, {dtubv88(i)});
  DECLARE(INLINE_CONVERSION, bv88, bvdouble, $si2fp, {sbv88td(i)});
  DECLARE(INLINE_CONVERSION, bv88, bvdouble, $ui2fp, {ubv88td(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv64, $fp2si, {dtsi64(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv64, $fp2ui, {dtubv64(i)});
  DECLARE(INLINE_CONVERSION, bv64, bvdouble, $si2fp, {sbv64td(i)});
  DECLARE(INLINE_CONVERSION, bv64, bvdouble, $ui2fp, {ubv64td(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv56, $fp2si, {dtsi56(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv56, $fp2ui, {dtubv56(i)});
  DECLARE(INLINE_CONVERSION, bv56, bvdouble, $si2fp, {sbv56td(i)});
  DECLARE(INLINE_CONVERSION, bv56, bvdouble, $ui2fp, {ubv56td(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv48, $fp2si, {dtsi48(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv48, $fp2ui, {dtubv48(i)});
  DECLARE(INLINE_CONVERSION, bv48, bvdouble, $si2fp, {sbv48td(i)});
  DECLARE(INLINE_CONVERSION, bv48, bvdouble, $ui2fp, {ubv48td(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv40, $fp2si, {dtsi40(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv40, $fp2ui, {dtubv40(i)});
  DECLARE(INLINE_CONVERSION, bv40, bvdouble, $si2fp, {sbv40td(i)});
  DECLARE(INLINE_CONVERSION, bv40, bvdouble, $ui2fp, {ubv40td(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv32, $fp2si, {dtsi32(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv32, $fp2ui, {dtubv32(i)});
  DECLARE(INLINE_CONVERSION, bv32, bvdouble, $si2fp, {sbv32td(i)});
  DECLARE(INLINE_CONVERSION, bv32, bvdouble, $ui2fp, {ubv32td(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv24, $fp2si, {dtsi24(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv24, $fp2ui, {dtubv24(i)});
  DECLARE(INLINE_CONVERSION, bv24, bvdouble, $si2fp, {sbv24td(i)});
  DECLARE(INLINE_CONVERSION, bv24, bvdouble, $ui2fp, {ubv24td(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv16, $fp2si, {dtsi16(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv16, $fp2ui, {dtubv16(i)});
  DECLARE(INLINE_CONVERSION, bv16, bvdouble, $si2fp, {sbv16td(i)});
  DECLARE(INLINE_CONVERSION, bv16, bvdouble, $ui2fp, {ubv16td(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv8, $fp2si, {dtsi8(i)});
  DECLARE(INLINE_CONVERSION, bvdouble, bv8, $fp2ui, {dtubv8(i)});
  DECLARE(INLINE_CONVERSION, bv8, bvdouble, $si2fp, {sbv8td(i)});
  DECLARE(INLINE_CONVERSION, bv8, bvdouble, $ui2fp, {ubv8td(i)});
  
  D("function {:builtin \"(_ fp.to_sbv 64) RNE\"} $round.rne.bvdouble(bvdouble) returns (bv64);");
  D("function {:builtin \"(_ fp.to_sbv 64) RNA\"} $round.rna.bvdouble(bvdouble) returns (bv64);");
  D("function {:builtin \"(_ fp.to_sbv 64) RTN\"} $floor.bvdouble(bvdouble) returns (bv64);");
  D("function {:builtin \"(_ fp.to_sbv 64) RTP\"} $ceil.bvdouble(bvdouble) returns (bv64);");
  D("function {:builtin \"(_ fp.to_sbv 64) RTZ\"} $trunc.bvdouble(bvdouble) returns (bv64);");
  
  #if BUILD_64
    D("function {:builtin \"(_ fp.to_sbv 64) RNA\"} $lround.bvdouble(bvdouble) returns (bv64);");
  
  #else
    D("function {:builtin \"(_ fp.to_sbv 32) RNA\"} $lround.bvdouble(bvdouble) returns (bv32);");

  #endif
  
#endif

  // Memory Model
  D("const $GLOBALS_BOTTOM: ref;");
  D("const $EXTERNS_BOTTOM: ref;");
  D("const $MALLOC_TOP: ref;");
  D("function {:inline} $isExternal(p: ref) returns (bool) {$slt.ref.bool(p,$EXTERNS_BOTTOM)}");

  D("function {:inline} $load.i128(M: [ref] i128, p: ref) returns (i128) { M[p] }");
  D("function {:inline} $load.i96(M: [ref] i96, p: ref) returns (i96) { M[p] }");
  D("function {:inline} $load.i88(M: [ref] i88, p: ref) returns (i88) { M[p] }");
  D("function {:inline} $load.i64(M: [ref] i64, p: ref) returns (i64) { M[p] }");
  D("function {:inline} $load.i56(M: [ref] i56, p: ref) returns (i56) { M[p] }");
  D("function {:inline} $load.i48(M: [ref] i48, p: ref) returns (i48) { M[p] }");
  D("function {:inline} $load.i40(M: [ref] i40, p: ref) returns (i40) { M[p] }");
  D("function {:inline} $load.i32(M: [ref] i32, p: ref) returns (i32) { M[p] }");
  D("function {:inline} $load.i24(M: [ref] i24, p: ref) returns (i24) { M[p] }");
  D("function {:inline} $load.i16(M: [ref] i16, p: ref) returns (i16) { M[p] }");
  D("function {:inline} $load.i8(M: [ref] i8, p: ref) returns (i8) { M[p] }");

  D("function {:inline} $load.bv128(M: [ref] bv128, p: ref) returns (bv128) { M[p] }");
  D("function {:inline} $load.bv96(M: [ref] bv96, p: ref) returns (bv96) { M[p] }");
  D("function {:inline} $load.bv88(M: [ref] bv88, p: ref) returns (bv88) { M[p] }");
  D("function {:inline} $load.bv64(M: [ref] bv64, p: ref) returns (bv64) { M[p] }");
  D("function {:inline} $load.bv56(M: [ref] bv56, p: ref) returns (bv56) { M[p] }");
  D("function {:inline} $load.bv48(M: [ref] bv48, p: ref) returns (bv48) { M[p] }");
  D("function {:inline} $load.bv40(M: [ref] bv40, p: ref) returns (bv40) { M[p] }");
  D("function {:inline} $load.bv32(M: [ref] bv32, p: ref) returns (bv32) { M[p] }");
  D("function {:inline} $load.bv24(M: [ref] bv24, p: ref) returns (bv24) { M[p] }");
  D("function {:inline} $load.bv16(M: [ref] bv16, p: ref) returns (bv16) { M[p] }");
  D("function {:inline} $load.bv8(M: [ref] bv8, p: ref) returns (bv8) { M[p] }");

  D("function {:inline} $load.bytes.bv128(M: [ref] bv8, p: ref) returns (bv128)"
    "{ $load.bytes.bv64(M, $add.ref(p, $8.ref)) ++ $load.bytes.bv64(M, p) }");
  D("function {:inline} $load.bytes.bv96(M: [ref] bv8, p: ref) returns (bv96)"
    "{ $load.bytes.bv64(M, $add.ref(p, $4.ref)) ++ $load.bytes.bv32(M, p) }");
  D("function {:inline} $load.bytes.bv88(M: [ref] bv8, p: ref) returns (bv88)"
    "{ $load.bytes.bv56(M, $add.ref(p, $4.ref)) ++ $load.bytes.bv32(M, p) }");
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
  D("function {:inline} $store.i88(M: [ref] i88, p: ref, v: i88) returns ([ref] i88) { M[p := v] }");
  D("function {:inline} $store.i64(M: [ref] i64, p: ref, v: i64) returns ([ref] i64) { M[p := v] }");
  D("function {:inline} $store.i56(M: [ref] i56, p: ref, v: i56) returns ([ref] i56) { M[p := v] }");
  D("function {:inline} $store.i48(M: [ref] i48, p: ref, v: i48) returns ([ref] i48) { M[p := v] }");
  D("function {:inline} $store.i40(M: [ref] i40, p: ref, v: i40) returns ([ref] i40) { M[p := v] }");
  D("function {:inline} $store.i32(M: [ref] i32, p: ref, v: i32) returns ([ref] i32) { M[p := v] }");
  D("function {:inline} $store.i24(M: [ref] i24, p: ref, v: i24) returns ([ref] i24) { M[p := v] }");
  D("function {:inline} $store.i16(M: [ref] i16, p: ref, v: i16) returns ([ref] i16) { M[p := v] }");
  D("function {:inline} $store.i8(M: [ref] i8, p: ref, v: i8) returns ([ref] i8) { M[p := v] }");

  D("function {:inline} $store.bv128(M: [ref] bv128, p: ref, v: bv128) returns ([ref] bv128) { M[p := v] }");
  D("function {:inline} $store.bv96(M: [ref] bv96, p: ref, v: bv96) returns ([ref] bv96) { M[p := v] }");
  D("function {:inline} $store.bv88(M: [ref] bv88, p: ref, v: bv88) returns ([ref] bv88) { M[p := v] }");
  D("function {:inline} $store.bv64(M: [ref] bv64, p: ref, v: bv64) returns ([ref] bv64) { M[p := v] }");
  D("function {:inline} $store.bv56(M: [ref] bv56, p: ref, v: bv56) returns ([ref] bv56) { M[p := v] }");
  D("function {:inline} $store.bv48(M: [ref] bv48, p: ref, v: bv48) returns ([ref] bv48) { M[p := v] }");
  D("function {:inline} $store.bv40(M: [ref] bv40, p: ref, v: bv40) returns ([ref] bv40) { M[p := v] }");
  D("function {:inline} $store.bv32(M: [ref] bv32, p: ref, v: bv32) returns ([ref] bv32) { M[p := v] }");
  D("function {:inline} $store.bv24(M: [ref] bv24, p: ref, v: bv24) returns ([ref] bv24) { M[p := v] }");
  D("function {:inline} $store.bv16(M: [ref] bv16, p: ref, v: bv16) returns ([ref] bv16) { M[p := v] }");
  D("function {:inline} $store.bv8(M: [ref] bv8, p: ref, v: bv8) returns ([ref] bv8) { M[p := v] }");

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
  D("function {:inline} $store.bytes.bv88(M:[ref]bv8, p:ref, v:bv88) returns ([ref]bv8){"
    "M[p := v[8:0]][$add.ref(p, $1.ref) := v[16:8]]"
    "[$add.ref(p, $2.ref) := v[24:16]][$add.ref(p, $3.ref) := v[32:24]]"
    "[$add.ref(p, $4.ref) := v[40:32]][$add.ref(p, $5.ref) := v[48:40]]"
    "[$add.ref(p, $6.ref) := v[56:48]][$add.ref(p, $7.ref) := v[64:56]]"
    "[$add.ref(p, $7.ref) := v[72:64]][$add.ref(p, $8.ref) := v[80:72]]"
    "[$add.ref(p, $9.ref) := v[88:80]]}");
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

  #if FLOAT_ENABLED
  D("function {:inline} $load.bvfloat(M: [ref] bvfloat, p: ref) returns (bvfloat) { M[p] }");
  D("function {:inline} $store.bvfloat(M: [ref] bvfloat, p: ref, v: bvfloat) returns ([ref] bvfloat) { M[p := v] }");

  D("function {:inline} $load.bvdouble(M: [ref] bvdouble, p: ref) returns (bvdouble) { M[p] }");
  D("function {:inline} $store.bvdouble(M: [ref] bvdouble, p: ref, v: bvdouble) returns ([ref] bvdouble) { M[p := v] }");

  D("function {:inline} $store.bytes.bvfloat(M:[ref]bv8, p:ref, v:bvfloat) returns ([ref]bv8) {"
    "$store.bytes.bv32(M, p, $fp2ui.bvfloat.bv32(v))}");
  D("function {:inline} $store.bytes.bvdouble(M:[ref]bv8, p:ref, v:bvdouble) returns ([ref]bv8) {"
    "$store.bytes.bv64(M, p, $fp2ui.bvdouble.bv64(v))}");

  D("function {:inline} $load.bytes.bvfloat(M: [ref] bv8, p: ref) returns (bvfloat) {"
    "$ui2fp.bv32.bvfloat($load.bytes.bv32(M, p))}");
  D("function {:inline} $load.bytes.bvdouble(M: [ref] bv8, p: ref) returns (bvdouble) {"
    "$ui2fp.bv64.bvdouble($load.bytes.bv64(M, p))}");
  #endif

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
  DECLARE(RECORD_PROC, i88);
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
  DECLARE(RECORD_PROC, bv88);
  DECLARE(RECORD_PROC, bv96);
  DECLARE(RECORD_PROC, bv128);
  DECLARE(RECORD_PROC, ref);
  DECLARE(RECORD_PROC, float);
  #if FLOAT_ENABLED
  DECLARE(RECORD_PROC, bvfloat);
  DECLARE(RECORD_PROC, bvdouble);
  #endif

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
    "  $allocatedCounter := $allocatedCounter + 1;\n"
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
    "  p := $CurrAddr;\n"
    "  havoc $CurrAddr;\n"
    "  if ($sgt.ref.bool(n, $0.ref)) {\n"
    "    assume $sge.ref.bool($sub.ref($CurrAddr, n), p);\n"
    "    assume $sgt.ref.bool($CurrAddr, $0.ref) && $slt.ref.bool($CurrAddr, $MALLOC_TOP);\n"
    "    assume $Size(p) == n;\n"
    "    assume (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);\n"
    "  } else {\n"
    "    assume $sle.ref.bool($add.ref(p, $1.ref), $CurrAddr);\n"
    "    assume $Size(p) == $1.ref;\n"
    "    assume $eq.ref.bool($base(p), p);\n"
    "  }\n"
    "  $Alloc[p] := true;\n"
    "}\n");

  D("procedure $free(p: ref)\n"
    "modifies $Alloc, $allocatedCounter;\n"
    "{\n"
    "  if ($ne.ref.bool(p, $0.ref)) {\n"
    "    assert {:valid_free} $eq.ref.bool($base(p), p);\n"
    "    assert {:valid_free} $Alloc[p] == true;\n"
    "    assert {:valid_free} $sgt.ref.bool(p, $0.ref);\n"
    "    $Alloc[p] := false;\n"
    "    $allocatedCounter := $allocatedCounter - 1;\n"
    "  }\n"
    "}\n");

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
  D("var $Alloc: [ref] bool;");
  D("var $Size: [ref] ref;\n");

  D("procedure $galloc(base_addr: ref, size: ref);\n"
    "modifies $Alloc, $Size;"
    "ensures $Size[base_addr] == size;\n"
    "ensures (forall addr: ref :: {$base(addr)} $sle.ref.bool(base_addr, addr) && $slt.ref.bool(addr, $add.ref(base_addr, size)) ==> $base(addr) == base_addr);\n"
    "ensures $Alloc[base_addr];\n"
    "ensures (forall q: ref :: {$Size[q]} q != base_addr ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != base_addr ==> $Alloc[q] == old($Alloc[q]));\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $sgt.ref.bool(p, $0.ref);\n"
    "ensures $slt.ref.bool(p, $MALLOC_TOP);\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: ref :: old($Alloc[q]) ==> ($slt.ref.bool($add.ref(p, n), q) || $sgt.ref.bool(p, $add.ref(q, $Size[q]))));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $sge.ref.bool(n, $0.ref) ==> (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);\n");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc, $allocatedCounter;\n"
    "requires $eq.ref.bool(p, $0.ref) || ($eq.ref.bool($base(p), p) && $Alloc[p]);\n"
    "requires $sgt.ref.bool(p, $0.ref);\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> !$Alloc[p];\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> $allocatedCounter == old($allocatedCounter) - 1;\n");

#else // NO_REUSE does not reuse previously-allocated addresses
  D("var $Alloc: [ref] bool;");
  D("function $Size(ref) returns (ref);");
  D("var $CurrAddr:ref;\n");

  D("procedure $galloc(base_addr: ref, size: ref);\n"
    "modifies $Alloc;"
    "ensures $Size(base_addr) == size;\n"
    "ensures (forall addr: ref :: {$base(addr)} $sle.ref.bool(base_addr, addr) && $slt.ref.bool(addr, $add.ref(base_addr, size)) ==> $base(addr) == base_addr);\n"
    "ensures $Alloc[base_addr];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != base_addr ==> $Alloc[q] == old($Alloc[q]));\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $Alloc, $CurrAddr;\n"
    "ensures p == old($CurrAddr);\n"
    "ensures $sgt.ref.bool(n, $0.ref) ==> $sle.ref.bool($add.ref(old($CurrAddr), n), $CurrAddr);\n"
    "ensures $sgt.ref.bool(n, $0.ref) ==> $Size(p) == n;\n"
    "ensures $sgt.ref.bool(n, $0.ref) ==> (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);\n"
    "ensures !$sgt.ref.bool(n, $0.ref) ==> $sle.ref.bool($add.ref(old($CurrAddr), $1.ref), $CurrAddr);\n"
    "ensures !$sgt.ref.bool(n, $0.ref) ==> $Size(p) == $1.ref;\n"
    "ensures !$sgt.ref.bool(n, $0.ref) ==> $eq.ref.bool($base(p), p);\n"
    "ensures $Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc, $allocatedCounter;\n"
    "requires $eq.ref.bool(p, $0.ref) || ($eq.ref.bool($base(p), p) && $Alloc[p]);\n"
    "requires $sgt.ref.bool(p, $0.ref);\n"
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
    "  p := $CurrAddr;\n"
    "  havoc $CurrAddr;\n"
    "  if ($sgt.ref.bool(n, $0.ref)) {\n"
    "    assume $sge.ref.bool($sub.ref($CurrAddr, n), p);\n"
    "    assume $sgt.ref.bool($CurrAddr, $0.ref) && $slt.ref.bool($CurrAddr, $MALLOC_TOP);\n"
    "  } else {\n"
    "    assume $sle.ref.bool($add.ref(p, $1.ref), $CurrAddr);\n"
    "  }\n"
    "}\n");

  D("procedure $free(p: ref);\n");

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
  D("var $Alloc: [ref] bool;");
  D("var $Size: [ref] ref;\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $sgt.ref.bool(p, $0.ref);\n"
    "ensures $slt.ref.bool(p, $MALLOC_TOP);\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: ref :: old($Alloc[q]) ==> ($slt.ref.bool($add.ref(p, n), q) || $sgt.ref.bool(p, $add.ref(q, $Size[q]))));\n"
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
    "ensures p == old($CurrAddr);\n"
    "ensures $sgt.ref.bool(n, $0.ref) ==> $sle.ref.bool($add.ref(old($CurrAddr), n), $CurrAddr);\n"
    "ensures !$sgt.ref.bool(n, $0.ref) ==> $sle.ref.bool($add.ref(old($CurrAddr), $1.ref), $CurrAddr);\n");

  D("procedure $free(p: ref);\n");
#endif
#endif

#undef D
}

#if MEMORY_SAFETY
// The size parameter represents number of bytes that are being accessed
void __SMACK_check_memory_safety(void* pointer, unsigned long size) {
  void* sizeRef = (void*)size;
  __SMACK_code("assert {:valid_deref} $Alloc[$base(@)] == true;", pointer);
  __SMACK_code("assert {:valid_deref} $sle.ref.bool($base(@), @);", pointer, pointer);
#if MEMORY_MODEL_NO_REUSE_IMPLS
  __SMACK_code("assert {:valid_deref} $sle.ref.bool($add.ref(@, @), $add.ref($base(@), $Size($base(@))));", pointer, sizeRef, pointer, pointer);
#elif MEMORY_MODEL_REUSE
  __SMACK_code("assert {:valid_deref} $sle.ref.bool($add.ref(@, @), $add.ref($base(@), $Size[$base(@)]));", pointer, sizeRef, pointer, pointer);
#else
  __SMACK_code("assert {:valid_deref} $sle.ref.bool($add.ref(@, @), $add.ref($base(@), $Size($base(@))));", pointer, sizeRef, pointer, pointer);
#endif
}

void __SMACK_check_memory_leak() {
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


#if MEMORY_SAFETY || SIGNED_INTEGER_OVERFLOW_CHECK
char *strcpy(char *dest, const char *src) {
  char *save = dest;
  while (*dest++ = *src++);
  return save;
}

size_t strlen(const char *str) {
  size_t count = 0;
  while (str[count] != 0) count++;
  return count;
}

char *strrchr(const char *src, int c) {
  char *result = (char *)0;

  while (*src != 0) {
    if (*src == c) {
      result = src;
    }
    src++;
  }
  return result;
}

size_t strspn(const char *cs, const char *ct) {
  size_t n;
  const char *p;
  for (n = 0; *cs; cs++, n++) {
    for (p = ct; *p && *p != *cs; p++);
    if (!*p) break;
  }
  return n;
}

unsigned long int strtoul(const char *nptr, char **endptr, int base) {
  if (__VERIFIER_nondet_int()) {
    if (endptr != 0) {
      *endptr = nptr;
    }
    return 0;
  } else {
    if (endptr != 0) {
      size_t size = strlen(nptr);
      *endptr = nptr + size;
    }
    return __VERIFIER_nondet_ulong();
  }
}

double strtod(const char *nptr, char **endptr) {
  if (__VERIFIER_nondet_int()) {
    if (endptr != 0) {
      *endptr = nptr;
    }
    return 0.0;
  } else {
    if (endptr != 0) {
      size_t size = strlen(nptr);
      *endptr = nptr + size;
    }
    return __VERIFIER_nondet_long();
  }
}

char *error_str = "xx";
char *strerror(int errnum) {
  error_str[0] = __VERIFIER_nondet_char();
  error_str[1] = __VERIFIER_nondet_char();
  return error_str;
}

char *env_value_str = "xx";
char *getenv(const char *name) {
  if (__VERIFIER_nondet_int()) {
    return 0;
  } else {
    env_value_str[0] = __VERIFIER_nondet_char();
    env_value_str[1] = __VERIFIER_nondet_char();
    return env_value_str;
  }
}

void *realloc (void *__ptr, size_t __size) {
  free(__ptr);
  return malloc(__size);
}
#endif

