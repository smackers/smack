#include <stdlib.h>
#include "smack.h"

void foo(int *x) {
  *x = *x + 10;
}

int main(void) {
  int *y = malloc(sizeof(int));
  int tmp = __SMACK_nondet();

  *y = 10;

  // using a dummy unreachable call, force DSA to analyze foo so
  // that __SMACK_code works properly
  assume(tmp == 0);
  if (tmp) foo(y);
  __SMACK_code("call foo(@);",y);

  assert(*y == 10);
}

