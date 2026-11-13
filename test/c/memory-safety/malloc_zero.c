#include "smack.h"
#include <stdlib.h>

// @expect verified

// malloc(0) never fails (SV-COMP) and, per C11 7.22.3, behaves as if the
// size were nonzero except that the pointer must not be used to access an
// object: freeing it is valid (basic/malloc_zero.c checks it is non-null
// and distinct; assertions are not checked under --check=memory-safety).
int main(void) {
  char *p = malloc(0);
  char *q = malloc(0);
  char *r = malloc(1);
  r[0] = 1;
  free(p);
  free(q);
  free(r);
  return 0;
}
