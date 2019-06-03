#include "smack.h"
#include <math.h>

// @expect error
// @flag --bit-precise

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double val = __VERIFIER_nondet_double();

  if (!__isnan(val) && !__isinf(val) && !__iszero(val)) {
    assert(ceil(val) >= val);
    assert(ceil(val) <= val + 0.5);
  }

  assert(ceil(0.0) == 0.0);
  assert(ceil(-0.0) == -0.0);
  int isNeg = __signbit(ceil(-0.0));
  assert(isNeg);

  assert(ceil(Inf) == Inf);
  assert(ceil(negInf) == negInf);

  assert(__isnan(ceil(NaN)));

  return 0;
}
