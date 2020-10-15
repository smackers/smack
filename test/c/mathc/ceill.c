#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  assert(ceill(2.1l) == 3.0l);

  long double val = __VERIFIER_nondet_long_double();

  if (!__isnanl(val) && !__isinfl(val) && !__iszerol(val)) {
    assert(ceill(val) >= val);
    assert(ceill(val) <= val + 1);
  }

  assert(ceill(0.0l) == 0.0l);
  assert(ceill(-0.0l) == -0.0l);
  int isNeg = __signbitl(ceill(-0.0l));
  assert(isNeg);

  assert(ceill(Inf) == Inf);
  assert(ceill(negInf) == negInf);

  assert(__isnanl(ceill(NaN)));

  return 0;
}
