#include "smack.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>

// @expect error

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float x = __VERIFIER_nondet_float();
  float y = __VERIFIER_nondet_float();

  if (!__isnanf(x) && !__isinff(x)) {
    if (!__isnanf(y) && !__isinff(y)) {
      float dim = fdimf(x, y);
      if (x > y) {
        assert(dim == x - y);
      } else {
        assert(dim < 0.0f);
      }
    }
  }

  if (!__isnanf(x)) {
    assert(fdimf(x, Inf) == 0.0f);
  }

  if (!__isnanf(y) && y < 0) {
    assert(fdimf(Inf, y) == Inf);
  }

  assert(__isnanf(fdimf(x, NaN)));
  assert(__isnanf(fdimf(NaN, y)));

  return 0;
}
