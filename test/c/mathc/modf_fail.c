#include "smack.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>

// @expect error
// @flag --integer-encoding=bit-vector

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double x = __VERIFIER_nondet_double();
  double fPart, iPart;

  if (!__isnan(x) && !__isinf(x) && !__iszero(x)) {
    fPart = modf(x, &iPart);
    if (x < 0) {
      assert(x < iPart);
      assert(x < fPart);
    } else {
      assert(x >= iPart);
      assert(x >= fPart);
    }
  }

  fPart = modf(0.0, &iPart);
  assert(iPart == 0.0 && fPart == 0.0);

  fPart = modf(-0.0, &iPart);
  assert(iPart == -0.0 && fPart == -0.0);

  fPart = modf(Inf, &iPart);
  assert(iPart == Inf && fPart == 0.0);

  fPart = modf(negInf, &iPart);
  assert(iPart == negInf && fPart == -0.0);

  fPart = modf(NaN, &iPart);
  assert(__isnan(iPart) && __isnan(fPart));

  return 0;
}
