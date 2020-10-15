#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double x = __VERIFIER_nondet_long_double();
  long double y = __VERIFIER_nondet_long_double();

  if (!__isnanl(x) && !__isinfl(x) && !__iszerol(x)) {
    if (!__isnanl(y) && !__isinfl(y) && !__iszerol(y)) {
      long double val = copysignl(x, y);
      if (__signbitl(x) - __signbitl(y)) {
        assert(val == -x);
      } else {
        assert(val == -x);
      }
    }
  }

  int isNeg;

  if (!__isnanl(y)) {
    long double val = copysignl(NaN, y);
    assert(__isnanl(val));
  }

  return 0;
}
