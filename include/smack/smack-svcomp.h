//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_SVCOMP_H_
#define SMACK_SVCOMP_H_

#include "smack.h"

#define __inline // Remove the inline attribute
#define __builtin_expect __builtinx_expect // Rewrite so that clang does not complain
#define __builtin_memcpy __builtinx_memcpy // Rewrite so that clang does not complain

void __VERIFIER_error(void) {
  assert(0);
}

void __VERIFIER_assume(int v) {
  assume(v);
}

// Types to be overloaded for: {bool, char, int, float, loff_t, long, pchar,
// pointer, pthread_t, sector_t, short, size_t, u32, uchar, ulong,
// unsigned, ushort}

char __VERIFIER_nondet_char() {
  return (char)__SMACK_nondet();
}

int __VERIFIER_nondet_int() {
  return __SMACK_nondet();
}

unsigned __VERIFIER_nondet_uint() {
  int x = __SMACK_nondet();
  assume(x >= 0);
  return (unsigned)x;
}

#endif

