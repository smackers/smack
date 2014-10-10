//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_SVCOMP_H_
#define SMACK_SVCOMP_H_

void __VERIFIER_error(void) {
  assert(0);
}

void __VERIFIER_assume(int v) {
  assume(v);
}

//Types to be overloaded for: {bool, char, int, float, loff_t, long, pchar, pointer, pthread_t, sector_t, short, size_t, u32, uchar, uint, ulong, unsigned, ushort}

char __VERIFIER_nondet_char() {
  return (char)__SMACK_nondet();
}

int __VERIFIER_nondet_int() {
  return __SMACK_nondet();
}

#endif
