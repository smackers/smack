#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect error
// @checkbpl grep "call foo("

// Boogie text calls foo by name. Inlining the one call the compiler can see
// would leave foo without callers, and it would be removed from under the text.
void foo(int *x) { *x = *x + 10; }

int main(void) {
  int *y = (int *)malloc(sizeof(int));
  int tmp = __VERIFIER_nondet_int();

  *y = 10;

  assume(tmp == 0);
  if (tmp)
    foo(y);
  __SMACK_code("call foo(@);", y);

  assert(*y == 10);
  return 0;
}
