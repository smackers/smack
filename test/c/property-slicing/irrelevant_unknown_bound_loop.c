#include "smack.h"
#include <assert.h>

// @expect verified
// Unknown trip count, no relevant effect.

int main(void) {
  int n = __VERIFIER_nondet_int();
  int scratch = 0;
  int i;
  int watched = 1;
  for (i = 0; i < n; i++) {
    scratch += i;
  }
  assert(watched == 1);
  return 0;
}
