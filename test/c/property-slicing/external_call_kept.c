#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect verified
// An undefined external is never elided: its effects are unknown.

extern int opaque(int);

int main(void) {
  int a = __VERIFIER_nondet_int();
  opaque(a);
  assert(1);
  return 0;
}
