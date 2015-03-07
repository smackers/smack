//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack-svcomp.h"

void __VERIFIER_error(void) {
  assert(0);
}

void __VERIFIER_assume(int v) {
  assume(v);
}

void exit(int x) {
  assume(0);
}

// Types to be overloaded for: {bool, float, loff_t, pchar,
// pthread_t, sector_t, size_t, u32}

char __VERIFIER_nondet_char(void) {
  return (char)__SMACK_nondet();
}

short __VERIFIER_nondet_short(void) {
  return (short)__SMACK_nondet();
}

int __VERIFIER_nondet_int(void) {
  return __SMACK_nondet();
}

long __VERIFIER_nondet_long(void) {
  return (long)__SMACK_nondet();
}

unsigned char __VERIFIER_nondet_uchar(void) {
  char x = (char)__SMACK_nondet();
  assume(x >= 0);
  return (unsigned char)x;
}

unsigned short __VERIFIER_nondet_ushort(void) {
  short x = (short)__SMACK_nondet();
  assume(x >= 0);
  return (unsigned short)x;
}

unsigned __VERIFIER_nondet_uint(void) {
  int x = __SMACK_nondet();
  assume(x >= 0);
  return (unsigned)x;
}

unsigned long __VERIFIER_nondet_ulong(void) {
  long x = (long)__SMACK_nondet();
  assume(x >= 0);
  return (unsigned long)x;
}

void* __VERIFIER_nondet_pointer(void) {
  return (void*)__SMACK_nondet();
}

