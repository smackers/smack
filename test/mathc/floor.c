#include "smack.h"
#include <math.h>

// @expect verified
// @flag --bit-precise

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  assert(floor(2.9) == 2.0);

  double val = __VERIFIER_nondet_double();

  if (!__isnan(val) && !__isinf(val) && !__iszero(val)) {
    assert(floor(val) <= val);
    assert(floor(val) >= val - 1);
  }

  assert(floor(0.0) == 0.0);
  assert(floor(-0.0) == -0.0);
  int isNeg = __signbit(floor(-0.0));
  assert(isNeg);

  assert(floor(Inf) == Inf);
  assert(floor(negInf) == negInf);

  assert(__isnan(floor(NaN)));

  return 0;
}
