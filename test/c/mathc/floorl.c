#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  assert(floorl(2.9l) == 2.0l);

  long double val = __VERIFIER_nondet_long_double();

  if (!__isnanl(val) && !__isinfl(val) && !__iszerol(val)) {
    assert(floorl(val) <= val);
    assert(floorl(val) >= val - 1);
  }

  assert(floorl(0.0l) == 0.0l);
  assert(floorl(-0.0l) == -0.0l);
  int isNeg = __signbitl(floorl(-0.0l));
  assert(isNeg);

  assert(floorl(Inf) == Inf);
  assert(floorl(negInf) == negInf);

  assert(__isnanl(floorl(NaN)));

  return 0;
}
