#include "smack.h"
#include <assert.h>

// @expect error
// The twin of ps_noreturn_call.c: control that gets past ldv_stop really can
// violate the assertion, so retaining the call must not hide the error.

void ldv_stop(void) {
  while (1) {
  }
}

int main(void) {
  int guard = __VERIFIER_nondet_int();
  if (!guard) {
    ldv_stop();
  }
  assert(guard != 1);
  return 0;
}
