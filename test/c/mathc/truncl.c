#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double val = __VERIFIER_nondet_long_double();

  if (!__isnanl(val) && !__isinfl(val) && !__iszerol(val)) {
    if (val > 0) {
      assert(truncl(val) <= val);
    } else {
      assert(truncl(val) >= val);
    }
  }

  assert(truncl(0.0l) == 0.0l);
  assert(truncl(-0.0l) == -0.0l);
  int isNeg = __signbitl(truncl(-0.0l));
  assert(isNeg);

  assert(truncl(Inf) == Inf);
  assert(truncl(negInf) == negInf);

  assert(__isnanl(truncl(NaN)));

  return 0;
}
