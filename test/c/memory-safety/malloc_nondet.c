#include "smack.h"
#include <stdlib.h>

// @expect verified

int main(void) {
  int x = __VERIFIER_nondet_int();
  assume(x != 0); // malloc(0) can return anything
  char *p = (char *)malloc(x);
  p[x - 1] = x;
  free(p);
  return 0;
}
