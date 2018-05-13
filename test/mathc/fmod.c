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
      double mod = fmod(x, y);
      if (x > 0 && y > 0 || x < 0 && y < 0) {
        assert(mod >= 0 && mod <= y);
      } else {
        assert(mod >= -y && mod <= 0);
      }
    }
  }

  if (!__isnan(y)) {
    assert(__isnan(fmod(Inf, y)));
    assert(__isnan(fmod(negInf, y)));
  }

  if (!__isnan(x)) {
    assert(__isnan(fmod(x, 0.0)));
    assert(__isnan(fmod(x, -0.0)));
  }

  if (!__isnan(x) && !__isinf(x)) {
    assert(fmod(x, Inf) == x);
    assert(fmod(x, negInf) == x);
  }
 
  if (!__isnan(y) && !__iszero(y)) {
    assert(fmod(0.0, y) == 0.0);
    assert(fmod(-0.0, y) == -0.0);
    int isNeg = __signbit(fmod(-0.0, y));
    assert(isNeg);
  }
 
  assert(__isnan(fmod(NaN, y)));
  assert(__isnan(fmod(x, NaN)));

  return 0;
}
