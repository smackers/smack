#include "smack.h"
#include <assert.h>

// @expect error
// @checkbpl grep -E ":= \(if.+then.+else.+\)"

void foo(int x) { assert(x); }

int main(void) {
  int c = __VERIFIER_nondet_int();
  assume(c == 2);
  foo(c != 2 ? 1 : 0);
}
