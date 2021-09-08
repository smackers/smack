#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double x = __VERIFIER_nondet_long_double();
  long double y = __VERIFIER_nondet_long_double();

  if (!__isnanl(x) && !__isinfl(x) && !__iszerol(x)) {
    if (!__isnanl(y) && !__isinfl(y) && !__iszerol(y)) {
      long double maxVal = fmaxl(x, y);
      if (x > y) {
        assert(maxVal == x);
      } else {
        assert(maxVal == y);
      }
    }
  }

  if (!__isnanl(y)) {
    assert(fmaxl(Inf, y) == Inf);
    assert(fmaxl(negInf, y) == y);
    assert(fmaxl(NaN, y) == y);
  }

  if (!__isnanl(x)) {
    assert(fmaxl(x, Inf) == Inf);
    assert(fmaxl(x, negInf) == x);
    assert(fmaxl(x, NaN) == x);
  }

  assert(__isnanl(fmaxl(NaN, NaN)));

  return 0;
}
