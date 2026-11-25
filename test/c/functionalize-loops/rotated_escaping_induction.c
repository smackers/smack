#include "smack.h"

// @expect verified
// @checkbpl grep -q lambda

// In a loop whose exit test follows the body, the header induction PHI seen
// after the loop holds the value of the last iteration that ran, one step
// short of the incremented value.
int main(void) {
  unsigned a[16];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 16);
  unsigned last = 0;

  // The guard is what lets ScalarEvolution bound the backedge count by n - 1.
  if (n >= 1) {
    unsigned i = 0;
    do {
      a[i] = 1;
      last = i;
      i++;
    } while (i < n);
  }

  __VERIFIER_assert(n == 0 || last == n - 1);
  return 0;
}
