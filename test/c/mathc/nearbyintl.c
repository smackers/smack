#include "smack.h"
#include <assert.h>
#include <fenv.h>
#include <math.h>

// @expect verified

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double a = -3.5l;
  long double b = -3.4999999999l;
  long double c = -3.5000000001l;
  long double d = 7.3l;

  fesetround(FE_TONEAREST);
  assert(nearbyintl(a) == -4.0l);
  assert(nearbyintl(b) == -3.0l);
  assert(nearbyintl(c) == -4.0l);
  assert(nearbyintl(d) == 7.0l);

  fesetround(FE_UPWARD);
  assert(nearbyintl(a) == -3.0l);
  assert(nearbyintl(b) == -3.0l);
  assert(nearbyintl(c) == -3.0l);
  assert(nearbyintl(d) == 8.0l);

  fesetround(FE_DOWNWARD);
  assert(nearbyintl(a) == -4.0l);
  assert(nearbyintl(b) == -4.0l);
  assert(nearbyintl(c) == -4.0l);
  assert(nearbyintl(d) == 7.0l);

  fesetround(FE_TOWARDZERO);
  assert(nearbyintl(a) == -3.0l);
  assert(nearbyintl(b) == -3.0l);
  assert(nearbyintl(c) == -3.0l);
  assert(nearbyintl(d) == 7.0l);

  assert(nearbyintl(0.0l) == 0.0l);
  assert(nearbyintl(-0.0l) == -0.0l);
  int isNeg = __signbitl(nearbyintl(-0.0l));
  assert(isNeg);

  assert(nearbyintl(Inf) == Inf);
  assert(nearbyintl(negInf) == negInf);

  assert(__isnanl(nearbyintl(NaN)));

  return 0;
}
