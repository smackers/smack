#include "smack.h"
#include <assert.h>
#include <fenv.h>
#include <math.h>

// @expect error

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double a = -2.5l;
  long double b = -2.4999999999l;
  long double c = -2.5000000001l;
  long double d = 8.3l;

  fesetround(FE_TONEAREST);
  assert(lrintl(a) == -2);
  assert(lrintl(b) == -2);
  assert(lrintl(c) == -3);
  assert(lrintl(d) == 8);

  fesetround(FE_UPWARD);
  assert(lrintl(a) == -2);
  assert(lrintl(b) == -1);
  assert(lrintl(c) == -2);
  assert(lrintl(d) == 9);

  fesetround(FE_DOWNWARD);
  assert(lrintl(a) == -3);
  assert(lrintl(b) == -3);
  assert(lrintl(c) == -3);
  assert(lrintl(d) == 8);

  fesetround(FE_TOWARDZERO);
  assert(lrintl(a) == -2);
  assert(lrintl(b) == -2);
  assert(lrintl(c) == -2);
  assert(lrintl(d) == 8);

  assert(lrintl(0.0l) == 0);
  assert(lrintl(-0.0l) == 0);

  return 0;
}
