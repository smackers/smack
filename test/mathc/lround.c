#include "smack.h"
#include <math.h>

// @expect verified

int main(void) {
  double val = __VERIFIER_nondet_double();

  if (!__isnan(val) && !__isinf(val) && !__iszero(val)) {
    //assert(lround(val) + 0.0 == ceil(val));
  }

  assert(lround(0.0) == 0);
  //assert(lround(-0.0) + 0.0 == 0);

  return 0;
}

