#include <stdlib.h>
#include "smack.h"

// @expect verified

int main(void) {
  int x = __VERIFIER_nondet_int();
  char *p = (char*)malloc(x);
  if (p != NULL) {
    p[x-1] = x;
    free(p);
  }
  return 0;
}

