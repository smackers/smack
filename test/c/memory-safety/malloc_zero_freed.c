#include "smack.h"
#include <stdlib.h>

// @flag --check=memleak
// @expect verified

int main(void) {
  char *p = malloc(0);
  char *q = calloc(0, 4);
  free(p);
  if (q != 0)
    free(q);
  return 0;
}
