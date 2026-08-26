#include "smack.h"
#include <assert.h>

// @expect verified
// The error block sits OUTSIDE the loop but is reachable only through it, and
// it is the function's only exit -- so it post-dominates the branch that
// decides to enter it, and non-termination-insensitive control dependence
// makes that branch, and with it `bad`, look irrelevant. The loop then holds
// nothing kept and is bypassed onto its unique exit block, which is the error.
// The original never leaves the loop (`bad` is assumed zero), so a report here
// is a false alarm.

int main(void) {
  int bad = __VERIFIER_nondet_int();
  int scratch = 0;
  __VERIFIER_assume(bad == 0);
  while (1) {
    if (bad) {
      assert(0);
      return 0;
    }
    scratch++;
  }
  return 0;
}
