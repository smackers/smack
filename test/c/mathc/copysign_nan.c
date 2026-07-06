#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  float y = __VERIFIER_nondet_float();
  __VERIFIER_assume(__isnanf(y));
  float val = copysignf(1.0f, y);
  assert(val == 1.0f || val == -1.0f);
  return 0;
}
