#include "smack.h"
#include <assert.h>

// @expect verified
// A property-irrelevant loop that may never terminate. Bypassing it ADDS the
// execution that reaches the assertion, which is the sound direction for
// reachability: the assertion still holds, so the verdict is unchanged. This
// test exists to pin that over-approximation down, not to claim the loop
// terminates.

int main(void) {
  int scratch = 0;
  int watched = 1;
  while (__VERIFIER_nondet_int()) {
    scratch++;
  }
  assert(watched == 1);
  return 0;
}
