#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  assert(remainderf(2.0f, 4.0f) == 2);
  assert(remainderf(2.00000001f, 4) == -1.99999999f);
  assert(remainderf(1.99999999f, 4) == -2.00000001f);

  float x = __VERIFIER_nondet_float();
  float y = __VERIFIER_nondet_float();

  if (!__isnanf(y)) {
    assert(__isnanf(remainderf(Inf, y)));
    assert(__isnanf(remainderf(negInf, y)));
  }

  if (!__isnanf(x)) {
    assert(__isnanf(remainderf(x, 0.0f)));
    assert(__isnanf(remainderf(x, -0.0f)));
  }

  assert(__isnanf(remainderf(NaN, y)));
  assert(__isnanf(remainderf(x, NaN)));

  return 0;
}
