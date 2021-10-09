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

  float a = -3.5f;
  float b = -3.4999999999f;
  float c = -3.5000000001f;
  float d = 7.3f;

  fesetround(FE_TONEAREST);
  assert(nearbyintf(a) == -4.0f);
  assert(nearbyintf(b) == -3.0f);
  assert(nearbyintf(c) == -4.0f);
  assert(nearbyintf(d) == 7.0f);

  fesetround(FE_UPWARD);
  assert(nearbyintf(a) == -3.0f);
  assert(nearbyintf(b) == -3.0f);
  assert(nearbyintf(c) == -3.0f);
  assert(nearbyintf(d) == 8.0f);

  fesetround(FE_DOWNWARD);
  assert(nearbyintf(a) == -4.0f);
  assert(nearbyintf(b) == -4.0f);
  assert(nearbyintf(c) == -4.0f);
  assert(nearbyintf(d) == 7.0f);

  fesetround(FE_TOWARDZERO);
  assert(nearbyintf(a) == -3.0f);
  assert(nearbyintf(b) == -3.0f);
  assert(nearbyintf(c) == -3.0f);
  assert(nearbyintf(d) == 7.0f);

  assert(nearbyintf(0.0f) == 0.0f);
  assert(nearbyintf(-0.0f) == -0.0f);
  int isNeg = __signbitf(nearbyintf(-0.0f));
  assert(isNeg);

  assert(nearbyintf(Inf) == Inf);
  assert(nearbyintf(negInf) == negInf);

  assert(__isnanf(nearbyintf(NaN)));

  return 0;
}
