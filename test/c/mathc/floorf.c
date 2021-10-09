#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  assert(floorf(2.9f) == 2.0f);

  float val = __VERIFIER_nondet_float();

  if (!__isnanf(val) && !__isinff(val) && !__iszerof(val)) {
    assert(floorf(val) <= val);
    assert(floorf(val) >= val - 1);
  }

  assert(floorf(0.0f) == 0.0f);
  assert(floorf(-0.0f) == -0.0f);
  int isNeg = __signbitf(floorf(-0.0f));
  assert(isNeg);

  assert(floorf(Inf) == Inf);
  assert(floorf(negInf) == negInf);

  assert(__isnanf(floorf(NaN)));

  return 0;
}
