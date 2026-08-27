#include "smack.h"

// @expect verified

// A global with no bytes still gets an address distinct from every other
// object's.
int g[0];
int h[2];
int k;

int main(void) {
  __VERIFIER_assert((char *)g != (char *)h);
  __VERIFIER_assert((char *)g != (char *)&k);
  h[0] = 7;
  __VERIFIER_assert(h[0] == 7);
  return 0;
}
