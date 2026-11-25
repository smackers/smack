#include "smack.h"
#include <assert.h>

// @expect verified
// A call whose result nothing relevant reads, and which touches no relevant
// region, may be dropped.

int square(int x) { return x * x + 1; }

int main(void) {
  int a = __VERIFIER_nondet_int();
  square(a);
  assert(1);
  return 0;
}
