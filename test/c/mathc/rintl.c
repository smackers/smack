#include "smack.h"
#include <assert.h>
#include <fenv.h>
#include <math.h>

// @expect verified

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double a = -4.5l;
  long double b = -4.4999999999l;
  long double c = -4.5000000001l;
  long double d = 5.3l;

  fesetround(FE_TONEAREST);
  assert(rintl(a) == -4.0l);
  assert(rintl(b) == -4.0l);
  assert(rintl(c) == -5.0l);
  assert(rintl(d) == 5.0l);

  fesetround(FE_UPWARD);
  assert(rintl(a) == -4.0l);
  assert(rintl(b) == -4.0l);
  assert(rintl(c) == -4.0l);
  assert(rintl(d) == 6.0l);

  fesetround(FE_DOWNWARD);
  assert(rintl(a) == -5.0l);
  assert(rintl(b) == -5.0l);
  assert(rintl(c) == -5.0l);
  assert(rintl(d) == 5.0l);

  fesetround(FE_TOWARDZERO);
  assert(rintl(a) == -4.0l);
  assert(rintl(b) == -4.0l);
  assert(rintl(c) == -4.0l);
  assert(rintl(d) == 5.0l);

  assert(rintl(0.0l) == 0.0l);
  assert(rintl(-0.0l) == -0.0l);
  int isNeg = __signbitl(rintl(-0.0l));
  assert(isNeg);

  assert(rintl(Inf) == Inf);
  assert(rintl(negInf) == negInf);

  assert(__isnanl(rintl(NaN)));

  return 0;
}
