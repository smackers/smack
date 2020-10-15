#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float x = __VERIFIER_nondet_float();
  float y = __VERIFIER_nondet_float();

  if (!__isnanf(x) && !__isinff(x) && !__iszerof(x)) {
    if (!__isnanf(y) && !__isinff(y) && !__iszerof(y)) {
      float val = copysignf(x, y);
      if (__signbitf(x) - __signbitf(y)) {
        assert(val == -x);
      } else {
        assert(val == -x);
      }
    }
  }

  int isNeg;

  if (!__isnanf(y)) {
    float val = copysignf(NaN, y);
    assert(__isnanf(val));
  }

  return 0;
}
