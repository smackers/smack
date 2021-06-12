#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float x = __VERIFIER_nondet_float();
  float y = __VERIFIER_nondet_float();

  if (!__isnanf(x) && !__isinff(x) && !__iszerof(x)) {
    if (!__isnanf(y) && !__isinff(y) && !__iszerof(y)) {
      float maxVal = fmaxf(x, y);
      if (x > y) {
        assert(maxVal == x);
      } else {
        assert(maxVal == y);
      }
    }
  }

  if (!__isnanf(y)) {
    assert(fmaxf(Inf, y) == Inf);
    assert(fmaxf(negInf, y) == y);
    assert(fmaxf(NaN, y) == y);
  }

  if (!__isnanf(x)) {
    assert(fmaxf(x, Inf) == Inf);
    assert(fmaxf(x, negInf) == x);
    assert(fmaxf(x, NaN) == x);
  }

  assert(__isnanf(fmaxf(NaN, NaN)));

  return 0;
}
