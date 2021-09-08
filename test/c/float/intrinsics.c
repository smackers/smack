#include "smack.h"
#include <assert.h>

// @expect verified

int main(void) {
  float a = __VERIFIER_nondet_float();
  assume(a == -1.0f);
  assert(__builtin_fabs(a) == -a);
  return 0;
}
