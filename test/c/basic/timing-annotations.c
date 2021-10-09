#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// This test ensures that the timing-annotations are respected
// and show up in the generated boogie.
// Currently, we just do the simplest thing and make sure that
// there is at least one instruction with expected cost.

// @flag --timing-annotations
// @expect verified
// @checkbpl grep "smack.InstTimingCost.Int64 1"

int foo(int a, int b) { return a + b; }

int main(void) {
  int a = 10;
  int b = 9;
  int c = foo(a, b);
  assert(c != 0);
  return 0;
}
