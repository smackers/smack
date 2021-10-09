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
      assert(fabs(val) == val);
    } else {
      assert(fabs(val) == -val);
    }
  }

  assert(fabs(0.0) == 0.0);
  assert(fabs(-0.0) == 0.0);
  int isNeg = __signbit(fabs(-0.0));
  assert(!isNeg);

  assert(fabs(Inf) == Inf);
  assert(fabs(negInf) == Inf);

  assert(__isnan(fabs(NaN)));

  return 0;
}
