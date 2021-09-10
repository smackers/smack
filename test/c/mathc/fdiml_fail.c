#include "smack.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>

// @expect error

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double x = __VERIFIER_nondet_long_double();
  long double y = __VERIFIER_nondet_long_double();

  if (!__isnanl(x) && !__isinfl(x)) {
    if (!__isnanl(y) && !__isinfl(y)) {
      long double dim = fdiml(x, y);
      if (x > y) {
        assert(dim == x - y);
      } else {
        assert(dim < 0.0l);
      }
    }
  }

  if (!__isnanl(x)) {
    assert(fdiml(x, Inf) == 0.0l);
  }

  if (!__isnanl(y) && y < 0) {
    assert(fdiml(Inf, y) == Inf);
  }

  assert(__isnanl(fdiml(x, NaN)));
  assert(__isnanl(fdiml(NaN, y)));

  return 0;
}
