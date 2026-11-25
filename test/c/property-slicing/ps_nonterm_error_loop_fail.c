#include "smack.h"
#include <assert.h>

// @expect error
// The twin of ps_nonterm_error_loop.c with the assumption dropped: the loop is
// now left whenever `bad` holds, and the error is real. Keeping the guard must
// not cost the error.

int main(void) {
  int bad = __VERIFIER_nondet_int();
  int scratch = 0;
  while (1) {
    if (bad) {
      assert(0);
      return 0;
    }
    scratch++;
  }
  return 0;
}
