#include "smack.h"

// @expect verified

// A 33-bit value stored through the byte-level memory model occupies five
// bytes: the prelude's $store.bytes.bv33 must zero-extend to 40 bits and
// $load.bytes.bv33 must truncate the five-byte concatenation back to 33 bits.
// Overwriting byte 4 sets bit 32, the sign bit of a signed _ExtInt(33).
int main(void) {
  _ExtInt(33) v = (_ExtInt(33))__VERIFIER_nondet_int();
  __VERIFIER_assume(v >= 0);
  _ExtInt(33) a[1];
  a[0] = v;
  unsigned char *c = (unsigned char *)a; // byte access collapses the region to bytes
  c[4] = 7;
  __VERIFIER_assert((unsigned)a[0] == (unsigned)v); // low 32 bits untouched
  __VERIFIER_assert(a[0] < 0);                      // bit 32 = low bit of 7
  return 0;
}
