#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float x = __VERIFIER_nondet_float();
  float y = __VERIFIER_nondet_float();

  if (!__isnanf(x) && !__isinff(x) && !__iszerof(x)) {
    if (!__isnanf(y) && !__isinff(y) && !__iszerof(y)) {
      float minVal = fminf(x, y);
      if (x < y) {
        assert(minVal == y);
      } else {
        assert(minVal == x);
      }
    }
  }

  if (!__isnanf(y)) {
    assert(fminf(Inf, y) == y);
    assert(fminf(negInf, y) == negInf);
    assert(fminf(NaN, y) == y);
  }

  if (!__isnanf(x)) {
    assert(fminf(x, Inf) == x);
    assert(fminf(x, negInf) == negInf);
    assert(fminf(x, NaN) == x);
  }

  assert(__isnanf(fminf(NaN, NaN)));

  return 0;
}
