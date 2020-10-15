#include "smack.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>

// @expect error
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float x = __VERIFIER_nondet_float();
  float fPart, iPart;

  if (!__isnanf(x) && !__isinff(x) && !__iszerof(x)) {
    fPart = modff(x, &iPart);
    if (x < 0) {
      assert(x <= iPart);
      assert(x <= fPart);
    } else {
      assert(x > iPart);
      assert(x > fPart);
    }
  }

  fPart = modff(0.0f, &iPart);
  assert(iPart == 0.0f && fPart == 0.0f);

  fPart = modff(-0.0f, &iPart);
  assert(iPart == -0.0f && fPart == -0.0f);

  fPart = modff(Inf, &iPart);
  assert(iPart == Inf && fPart == 0.0f);

  fPart = modff(negInf, &iPart);
  assert(iPart == negInf && fPart == -0.0f);

  fPart = modff(NaN, &iPart);
  assert(__isnanf(iPart) && __isnanf(fPart));

  return 0;
}
