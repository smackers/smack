#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect error

void foo(int *x) { *x = *x + 10; }

int main(void) {
  int *y = malloc(sizeof(int));
  int tmp = __VERIFIER_nondet_int();

  *y = 10;

  // using a dummy unreachable call, force DSA to analyze foo so
  // that __SMACK_code works properly
  assume(tmp == 0);
  if (tmp)
    foo(y);
  __SMACK_code("call foo(@);", y);

  assert(*y == 10);
}
