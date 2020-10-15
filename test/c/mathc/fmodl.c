#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double x = 2.0l;
  long double y = -8.5;

  long double a = 5.1;
  long double b = -3.0l;
  long double c = fmodl(a, b);
  assert(fabsl(c - 2.1) < 1e-8);

  if (!__isnanl(y)) {
    assert(__isnanl(fmodl(Inf, y)));
    assert(__isnanl(fmodl(negInf, y)));
  }

  if (!__isnanl(x)) {
    assert(__isnanl(fmodl(x, 0.0l)));
    assert(__isnanl(fmodl(x, -0.0l)));
  }

  if (!__isnanl(x) && !__isinfl(x)) {
    assert(fmodl(x, Inf) == x);
    assert(fmodl(x, negInf) == x);
  }

  if (!__isnanl(y) && !__iszerol(y)) {
    assert(fmodl(0.0l, y) == 0.0l);
    assert(fmodl(-0.0l, y) == -0.0l);
    int isNeg = __signbitl(fmodl(-0.0l, y));
    assert(isNeg);
  }

  assert(__isnanl(fmodl(NaN, y)));
  assert(__isnanl(fmodl(x, NaN)));

  return 0;
}
