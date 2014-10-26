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
// pthread_t, sector_t, short, size_t, u32, uchar, ulong,
// unsigned, ushort}

char __VERIFIER_nondet_char(void) {
  return (char)__SMACK_nondet();
}

int __VERIFIER_nondet_int(void) {
  return __SMACK_nondet();
}

unsigned __VERIFIER_nondet_uint(void) {
  int x = __SMACK_nondet();
  assume(x >= 0);
  return (unsigned)x;
}

void* __VERIFIER_nondet_pointer(void) {
  return (void*)__SMACK_nondet();
}

#endif

