#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float x = 2.0f;
  float y = -8.5;

  float a = 5.1;
  float b = -3.0f;
  float c = fmodf(a, b);
  assert(fabsf(c - 2.1) < 1e-8);

  if (!__isnanf(y)) {
    assert(__isnanf(fmodf(Inf, y)));
    assert(__isnanf(fmodf(negInf, y)));
  }

  if (!__isnanf(x)) {
    assert(__isnanf(fmodf(x, 0.0f)));
    assert(__isnanf(fmodf(x, -0.0f)));
  }

  if (!__isnanf(x) && !__isinff(x)) {
    assert(fmodf(x, Inf) == x);
    assert(fmodf(x, negInf) == x);
  }

  if (!__isnanf(y) && !__iszerof(y)) {
    assert(fmodf(0.0f, y) == 0.0f);
    assert(fmodf(-0.0f, y) == -0.0f);
    int isNeg = __signbitf(fmodf(-0.0f, y));
    assert(isNeg);
  }

  assert(__isnanf(fmodf(NaN, y)));
  assert(__isnanf(fmodf(x, NaN)));

  return 0;
}
