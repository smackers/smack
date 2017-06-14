#include <stdlib.h>
#include "smack.h"

// @expect error

int main(void) {
  int x = __VERIFIER_nondet_int();
  char *p = (char*)malloc(x);
  if (p != NULL) {
    p[x] = x;
    free(p);
  }
  return 0;
}

