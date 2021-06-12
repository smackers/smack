#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  assert(remainderl(2.0l, 4.0l) == 2);
  assert(remainderl(2.00000001l, 4) == -1.99999999l);
  assert(remainderl(1.99999999l, 4) == 1.99999999l);

  long double x = __VERIFIER_nondet_long_double();
  long double y = __VERIFIER_nondet_long_double();

  if (!__isnanl(y)) {
    assert(__isnanl(remainderl(Inf, y)));
    assert(__isnanl(remainderl(negInf, y)));
  }

  if (!__isnanl(x)) {
    assert(__isnanl(remainderl(x, 0.0l)));
    assert(__isnanl(remainderl(x, -0.0l)));
  }

  assert(__isnanl(remainderl(NaN, y)));
  assert(__isnanl(remainderl(x, NaN)));

  return 0;
}
