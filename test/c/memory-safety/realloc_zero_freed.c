#include "smack.h"
#include <stdlib.h>

// @flag --check=memleak
// @expect verified

// Freeing the size-zero block realloc(p, 0) returns, and the one
// realloc(NULL, 0) returns, accounts for both.
int main(void) {
  char *p = malloc(4);
  char *q = realloc(p, 0);
  char *r = realloc(0, 0);
  free(q);
  free(r);
  return 0;
}
