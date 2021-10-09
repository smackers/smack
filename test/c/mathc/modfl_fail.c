#include "smack.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>

// @expect error

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double x = __VERIFIER_nondet_long_double();
  long double fPart, iPart;

  if (!__isnanl(x) && !__isinfl(x) && !__iszerol(x)) {
    fPart = modfl(x, &iPart);
    if (x < 0) {
      assert(x <= iPart);
      assert(x <= fPart);
    } else {
      assert(x > iPart);
      assert(x > fPart);
    }
  }

  fPart = modfl(0.0l, &iPart);
  assert(iPart == 0.0l && fPart == 0.0l);

  fPart = modfl(-0.0l, &iPart);
  assert(iPart == -0.0l && fPart == -0.0l);

  fPart = modfl(Inf, &iPart);
  assert(iPart == Inf && fPart == 0.0l);

  fPart = modfl(negInf, &iPart);
  assert(iPart == negInf && fPart == -0.0l);

  fPart = modfl(NaN, &iPart);
  assert(__isnanl(iPart) && __isnanl(fPart));

  return 0;
}
