#include "smack.h"
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  float f = __VERIFIER_nondet_float();
  __VERIFIER_assume(!__isnanf(f));
  __VERIFIER_assume(0.0f < f);
  __VERIFIER_assume(!__isinff(f));
  float z = fmodf(f, 2.0f);
  __VERIFIER_assert(z <= 2.0f);
  return 0;
}
