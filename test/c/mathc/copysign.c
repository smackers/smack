#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double x = __VERIFIER_nondet_double();
  double y = __VERIFIER_nondet_double();

  if (!__isnan(x) && !__isinf(x) && !__iszero(x)) {
    if (!__isnan(y) && !__isinf(y) && !__iszero(y)) {
      double val = copysign(x, y);
      if (__signbit(x) - __signbit(y)) {
        assert(val == -x);
      } else {
        assert(val == x);
      }
    }
  }

  int isNeg;

  if (!__isnan(y)) {
    double val = copysign(NaN, y);
    assert(__isnan(val));
  }

  return 0;
}
