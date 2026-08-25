#include "smack.h"
#include <string.h>

// @expect error
// @flag --pointer-encoding=bit-vector --memory-intrinsic-threshold=8

// Scalar-expanded memcpy under bit-vector pointers: the per-offset updates
// must use pointer literals (`1bv64`), and the round trip of a 33-bit value
// through an 8-byte byte copy relies on the five-byte $load/$store.bytes.bv33.
int main(void) {
  _ExtInt(33) v = (_ExtInt(33))__VERIFIER_nondet_int();
  __VERIFIER_assume(v > 0);
  unsigned char buf[8];
  memcpy(buf, &v, 8);
  _ExtInt(33) w;
  memcpy(&w, buf, 8);
  __VERIFIER_assert(w == v + 1);
  return 0;
}
