#include "smack.h"
#include <assert.h>
#include <limits.h>

// @expect error

int main(void) {
  int v = __VERIFIER_nondet_int(); // we want to find the absolute value of v
  unsigned int r;                  // the result goes here
  int mask;
  assume(v < 0);
  mask = v >> (sizeof(int) * CHAR_BIT - 1);

  r = (v + mask) ^ mask;
  assert(r == v);
  return 0;
}
