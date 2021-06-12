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
      long double minVal = fminl(x, y);
      if (x < y) {
        assert(minVal == y);
      } else {
        assert(minVal == x);
      }
    }
  }

  if (!__isnanl(y)) {
    assert(fminl(Inf, y) == y);
    assert(fminl(negInf, y) == negInf);
    assert(fminl(NaN, y) == y);
  }

  if (!__isnanl(x)) {
    assert(fminl(x, Inf) == x);
    assert(fminl(x, negInf) == negInf);
    assert(fminl(x, NaN) == x);
  }

  assert(__isnanl(fminl(NaN, NaN)));

  return 0;
}
