#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double x = __VERIFIER_nondet_double();
  double y = __VERIFIER_nondet_double();

  if (!__isnan(x) && !__isinf(x) && !__iszero(x)) {
    if (!__isnan(y) && !__isinf(y) && !__iszero(y)) {
      double minVal = fmin(x, y);
      if (x < y) {
        assert(minVal == y);
      } else {
        assert(minVal == x);
      }
    }
  }

  if (!__isnan(y)) {
    assert(fmin(Inf, y) == y);
    assert(fmin(negInf, y) == negInf);
    assert(fmin(NaN, y) == y);
  }

  if (!__isnan(x)) {
    assert(fmin(x, Inf) == x);
    assert(fmin(x, negInf) == negInf);
    assert(fmin(x, NaN) == x);
  }

  assert(__isnan(fmin(NaN, NaN)));

  return 0;
}
