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
    if (val > 0) {
      assert(fabsl(val) == val);
    } else {
      assert(fabsl(val) == val);
    }
  }

  assert(fabsl(0.0l) == 0.0l);
  assert(fabsl(-0.0l) == 0.0l);
  int isNeg = __signbitl(fabsl(-0.0l));
  assert(!isNeg);

  assert(fabsl(Inf) == Inf);
  assert(fabsl(negInf) == Inf);

  assert(__isnanl(fabsl(NaN)));

  return 0;
}
