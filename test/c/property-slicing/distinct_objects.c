#include "smack.h"
#include <assert.h>

// @expect verified
// Two separate objects: the store to `other` cannot influence the load from
// `watched`, so the slicer may drop it. Removing it must not change the
// verdict.

int main(void) {
  int watched = 1;
  int other = 0;
  int *p = &other;
  int *q = &watched;
  *p = __VERIFIER_nondet_int();
  assert(*q == 1);
  return 0;
}
