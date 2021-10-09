#include "smack.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>

// @expect verified

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double x = __VERIFIER_nondet_double();
  double y = __VERIFIER_nondet_double();

  if (!__isnan(x) && !__isinf(x)) {
    if (!__isnan(y) && !__isinf(y)) {
      double dim = fdim(x, y);
      if (x > y) {
        assert(dim == x - y);
      } else {
        assert(dim == 0.0);
      }
    }
  }

  if (!__isnan(x)) {
    assert(fdim(x, Inf) == 0.0);
  }

  if (!__isnan(y) && y < 0) {
    assert(fdim(Inf, y) == Inf);
  }

  assert(__isnan(fdim(x, NaN)));
  assert(__isnan(fdim(NaN, y)));

  return 0;
}
