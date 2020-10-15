#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float val = __VERIFIER_nondet_float();

  if (!__isnanf(val) && !__isinff(val) && !__iszerof(val)) {
    float rval = roundf(val);
    assert(rval == floorf(val) || rval == ceilf(val));
  }

  assert(roundf(0.0f) == 0.0f);
  assert(roundf(-0.0f) > -0.0f);
  int isNeg = __signbitf(roundf(-0.0f));
  assert(isNeg);

  assert(roundf(Inf) == Inf);
  assert(roundf(negInf) == negInf);

  assert(__isnanf(roundf(NaN)));

  return 0;
}
