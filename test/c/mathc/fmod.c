#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double x = 2.0;
  double y = -8.5;

  double a = 5.1;
  double b = -3.0;
  double c = fmod(a, b);
  assert(fabs(c - 2.1) < 1e-8);

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
