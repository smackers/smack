#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  assert(ceilf(2.1f) == 3.0f);

  float val = __VERIFIER_nondet_float();

  if (!__isnanf(val) && !__isinff(val) && !__iszerof(val)) {
    assert(ceilf(val) >= val);
    assert(ceilf(val) <= val + 1);
  }

  assert(ceilf(0.0f) == 0.0f);
  assert(ceilf(-0.0f) == -0.0f);
  int isNeg = __signbitf(ceilf(-0.0f));
  assert(isNeg);

  assert(ceilf(Inf) == Inf);
  assert(ceilf(negInf) == negInf);

  assert(__isnanf(ceilf(NaN)));

  return 0;
}
