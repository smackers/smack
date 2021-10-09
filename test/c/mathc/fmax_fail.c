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
      double maxVal = fmax(x, y);
      if (x > y) {
        assert(maxVal == y);
      } else {
        assert(maxVal == x);
      }
    }
  }

  if (!__isnan(y)) {
    assert(fmax(Inf, y) == Inf);
    assert(fmax(negInf, y) == y);
    assert(fmax(NaN, y) == y);
  }

  if (!__isnan(x)) {
    assert(fmax(x, Inf) == Inf);
    assert(fmax(x, negInf) == x);
    assert(fmax(x, NaN) == x);
  }

  assert(__isnan(fmax(NaN, NaN)));

  return 0;
}
