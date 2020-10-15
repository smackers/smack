#include "smack.h"
#include <assert.h>
#include <fenv.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float a = -4.5f;
  float b = -4.4999999999f;
  float c = -4.5000000001f;
  float d = 5.3f;

  fesetround(FE_TONEAREST);
  assert(rintf(a) == -4.0f);
  assert(rintf(b) == -4.0f);
  assert(rintf(c) == -5.0f);
  assert(rintf(d) == 5.0f);

  fesetround(FE_UPWARD);
  assert(rintf(a) == -4.0f);
  assert(rintf(b) == -4.0f);
  assert(rintf(c) == -4.0f);
  assert(rintf(d) == 6.0f);

  fesetround(FE_DOWNWARD);
  assert(rintf(a) == -5.0f);
  assert(rintf(b) == -5.0f);
  assert(rintf(c) == -5.0f);
  assert(rintf(d) == 5.0f);

  fesetround(FE_TOWARDZERO);
  assert(rintf(a) == -4.0f);
  assert(rintf(b) == -4.0f);
  assert(rintf(c) == -4.0f);
  assert(rintf(d) == 5.0f);

  assert(rintf(0.0f) == 0.0f);
  assert(rintf(-0.0f) == -0.0f);
  int isNeg = __signbitf(rintf(-0.0f));
  assert(isNeg);

  assert(rintf(Inf) == Inf);
  assert(rintf(negInf) == negInf);

  assert(__isnanf(rintf(NaN)));

  return 0;
}
