#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error
// @flag --integer-encoding=bit-vector

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double val = __VERIFIER_nondet_double();

  if (!__isnan(val) && !__isinf(val) && !__iszero(val)) {
    double rval = round(val);
    assert(rval == floor(val) || rval == ceil(val));
  }

  assert(round(0.0) < 0.0);
  assert(round(-0.0) == -0.0);
  int isNeg = __signbit(round(-0.0));
  assert(isNeg);

  assert(round(Inf) == Inf);
  assert(round(negInf) == negInf);

  assert(__isnan(round(NaN)));

  return 0;
}
