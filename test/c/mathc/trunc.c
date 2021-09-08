#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double val = __VERIFIER_nondet_double();

  if (!__isnan(val) && !__isinf(val) && !__iszero(val)) {
    if (val > 0) {
      assert(trunc(val) <= val);
    } else {
      assert(trunc(val) >= val);
    }
  }

  assert(trunc(0.0) == 0.0);
  assert(trunc(-0.0) == -0.0);
  int isNeg = __signbit(trunc(-0.0));
  assert(isNeg);

  assert(trunc(Inf) == Inf);
  assert(trunc(negInf) == negInf);

  assert(__isnan(trunc(NaN)));

  return 0;
}
