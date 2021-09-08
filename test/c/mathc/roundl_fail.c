#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double val = __VERIFIER_nondet_long_double();

  if (!__isnanl(val) && !__isinfl(val) && !__iszerol(val)) {
    long double rval = roundl(val);
    assert(rval == floorl(val) || rval == ceill(val));
  }

  assert(roundl(0.0l) == 0.0l);
  assert(roundl(-0.0l) > -0.0l);
  int isNeg = __signbitl(roundl(-0.0l));
  assert(isNeg);

  assert(roundl(Inf) == Inf);
  assert(roundl(negInf) == negInf);

  assert(__isnanl(roundl(NaN)));

  return 0;
}
