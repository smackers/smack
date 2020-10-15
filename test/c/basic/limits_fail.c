#include "smack.h"
#include <assert.h>
#include <limits.h>

// @expect error

int main(void) {
  char x1 = __VERIFIER_nondet_char();
  assert(x1 >= SCHAR_MIN && x1 <= SCHAR_MAX);

  signed char x2 = __VERIFIER_nondet_signed_char();
  assert(x2 >= SCHAR_MIN && x2 <= SCHAR_MAX);

  unsigned char x3 = __VERIFIER_nondet_unsigned_char();
  assert(x3 >= 0 && x3 <= UCHAR_MAX);

  short x4 = __VERIFIER_nondet_short();
  assert(x4 >= SHRT_MIN && x4 <= SHRT_MAX);

  signed short x5 = __VERIFIER_nondet_signed_short();
  assert(x5 >= SHRT_MIN && x5 <= SHRT_MAX);

  signed short int x6 = __VERIFIER_nondet_signed_short_int();
  assert(x6 >= SHRT_MIN && x6 <= SHRT_MAX);

  unsigned short x7 = __VERIFIER_nondet_unsigned_short();
  assert(x7 >= 0 && x7 <= USHRT_MAX);

  unsigned short int x8 = __VERIFIER_nondet_unsigned_short_int();
  assert(x8 >= 0 && x8 <= USHRT_MAX);

  int x9 = __VERIFIER_nondet_int();
  assert(x9 >= INT_MIN && x9 <= INT_MAX);

  signed int x10 = __VERIFIER_nondet_signed_int();
  assert(x10 >= INT_MIN && x10 <= INT_MAX);

  unsigned x11 = __VERIFIER_nondet_unsigned();
  assert(x11 >= 0 && x11 <= UINT_MAX);

  unsigned int x12 = __VERIFIER_nondet_unsigned_int();
  assert(x12 >= 0 && x12 <= UINT_MAX);

  long x13 = __VERIFIER_nondet_long();
  assert(x13 >= LONG_MIN && x13 <= LONG_MAX);

  long int x14 = __VERIFIER_nondet_long_int();
  assert(x14 >= LONG_MIN && x14 <= LONG_MAX);

  signed long x15 = __VERIFIER_nondet_signed_long();
  assert(x15 >= LONG_MIN && x15 <= LONG_MAX);

  signed long int x16 = __VERIFIER_nondet_signed_long_int();
  assert(x16 >= LONG_MIN && x16 <= LONG_MAX);

  unsigned long x17 = __VERIFIER_nondet_unsigned_long();
  assert(x17 >= 0 && x17 <= ULONG_MAX);

  unsigned long int x18 = __VERIFIER_nondet_unsigned_long_int();
  assert(x18 >= 0 && x18 <= ULONG_MAX);

  long long x19 = __VERIFIER_nondet_long_long();
  assert(x19 >= LLONG_MIN && x19 <= LLONG_MAX);

  long long int x20 = __VERIFIER_nondet_long_long_int();
  assert(x20 >= LLONG_MIN && x20 <= LLONG_MAX);

  signed long long x21 = __VERIFIER_nondet_signed_long_long();
  assert(x21 >= LLONG_MIN && x21 <= LLONG_MAX);

  signed long long int x22 = __VERIFIER_nondet_signed_long_long_int();
  assert(x22 >= LLONG_MIN && x22 <= LLONG_MAX);

  unsigned long long x23 = __VERIFIER_nondet_unsigned_long_long();
  assert(x23 >= 0 && x23 <= ULLONG_MAX);

  unsigned long long int x24 = __VERIFIER_nondet_unsigned_long_long_int();
  assert(x24 >= 0 && x24 <= ULLONG_MAX);

  // Used in SVCCOMP benchmarks
  _Bool x25 = __VERIFIER_nondet_bool();
  assert(x25 == 0 || x25 == 1);

  unsigned char x26 = __VERIFIER_nondet_uchar();
  assert(x26 >= 0 && x26 <= UCHAR_MAX);

  unsigned short x27 = __VERIFIER_nondet_ushort();
  assert(x27 >= 0 && x27 <= USHRT_MAX);

  unsigned int x28 = __VERIFIER_nondet_uint();
  assert(x28 >= 0 && x28 <= UINT_MAX);

  unsigned long x29 = __VERIFIER_nondet_ulong();
  assert(x29 >= 1 && x29 <= ULONG_MAX);

  return 0;
}
