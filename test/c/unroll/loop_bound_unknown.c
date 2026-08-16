#include "smack.h"

// @expect verified
// @checkout grep -F "main: its bound cannot be determined statically"

// A symbolic trip count. This is the case that makes the choice of
// ScalarEvolution query matter: getConstantMaxBackedgeTakenCount would happily
// answer here, but only by falling back on the range of `int`, reporting a
// bound of 2147483647 that is true and useless. getSmallConstantTripCount
// declines instead, which is what lets the pass say so honestly.
//
// The assume keeps the loop from exiting within the unroll bound, so
// --fail-on-loop-exit does not fire and the expected result stays "verified".

int main(void) {
  int n = __VERIFIER_nondet_int();
  int i;
  int b = 0;

  assume(n > 100);

  for (i = 0; i < n; i++)
    b++;

  return b;
}
