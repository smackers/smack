#include "smack.h"
#include <assert.h>
#include <math.h>

//@expect error

int main(void) {
  double f = __VERIFIER_nondet_double();
  assume(isfinite(f));
  assert(f + 0.0 != f);
  return 0;
}
