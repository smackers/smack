#include "smack.h"
#include <assert.h>

// @expect error
// The error lives inside a callee whose result is unused: MayReachError must
// keep the call.

void may_fail(int x) {
  if (x == 3) {
    assert(0);
  }
}

int main(void) {
  int a = __VERIFIER_nondet_int();
  may_fail(a);
  return 0;
}
