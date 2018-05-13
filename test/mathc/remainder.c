#include "smack.h"
#include <math.h>

// @expect verified

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double x = __VERIFIER_nondet_double();
  double y = __VERIFIER_nondet_double();

  if (!__isnan(x) && !__isinf(x) && !__iszero(x)) {
    if (!__isnan(y) && !__isinf(y) && !__iszero(y)) {
      double rem = remainder(x, y);
      if (x > 0 && y > 0 || x < 0 && y < 0) {
        assert(rem >= 0 && rem <= y);
      } else {
        assert(rem >= -y && rem <= 0);
      }
    }
  }

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
