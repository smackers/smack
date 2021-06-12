#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  assert(remainder(2, 4) == 2);
  assert(remainder(2.00000001, 4) == -1.99999999);
  assert(remainder(1.99999999, 4) == 1.99999999);

  double x = __VERIFIER_nondet_double();
  double y = __VERIFIER_nondet_double();

  if (!__isnan(y)) {
    assert(__isnan(remainder(Inf, y)));
    assert(__isnan(remainder(negInf, y)));
  }

  if (!__isnan(x)) {
    assert(__isnan(remainder(x, 0.0)));
    assert(__isnan(remainder(x, -0.0)));
  }

  assert(__isnan(remainder(NaN, y)));
  assert(__isnan(remainder(x, NaN)));

  return 0;
}
