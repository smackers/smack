#include "smack.h"
#include <string.h>

// @expect verified
// @flag --pointer-encoding=bit-vector --memory-intrinsic-threshold=8

// Scalar-expanded memcpy under bit-vector pointers: the per-offset updates
// must use pointer literals (`1bv64`); a value is copied through
// a byte buffer and back.
int main(void) {
  unsigned short v = __VERIFIER_nondet_ushort();
  __VERIFIER_assume(v > 0);
  unsigned char buf[8];
  memcpy(buf, &v, sizeof(v));
  unsigned short w;
  memcpy(&w, buf, sizeof(v));
  __VERIFIER_assert(w == v);
  return 0;
}
