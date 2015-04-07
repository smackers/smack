//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack-svcomp.h"

void __VERIFIER_error(void) {
  __VERIFIER_assert(0);
}

void exit(int x) {
  __VERIFIER_assume(0);
}

// Types to be overloaded for: {bool, float, loff_t, pchar,
// pthread_t, sector_t, size_t, u32}

unsigned char __VERIFIER_nondet_uchar(void) {
  unsigned char x = __VERIFIER_nondet_unsigned_char();
  assume(x >= 0);
  return x;
}

unsigned short __VERIFIER_nondet_ushort(void) {
  unsigned short x = __VERIFIER_nondet_unsigned_short();
  assume(x >= 0);
  return x;
}

unsigned int __VERIFIER_nondet_uint(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  assume(x >= 0);
  return x;
}

unsigned long __VERIFIER_nondet_ulong(void) {
  unsigned long x = __VERIFIER_nondet_unsigned_long();
  assume(x >= 0);
  return x;
}

void* __VERIFIER_nondet_pointer(void) {
  return __VERIFIER_nondet();
}

