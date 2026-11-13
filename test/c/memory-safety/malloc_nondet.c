#include "smack.h"
#include <stdlib.h>

// @expect verified

int main(void) {
  int x = __VERIFIER_nondet_int();
  assume(x > 0); // p[x - 1] needs at least one byte
  char *p = (char *)malloc(x);
  p[x - 1] = x;
  free(p);
  return 0;
}
