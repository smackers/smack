#include "smack.h"
#include <stdlib.h>

// @flag --check=memleak
// @expect error

// realloc(p, 0) frees p and returns a size-zero block, which is a real
// allocation and must itself be freed; using the call as a spelling of
// free() leaks that block. See the comment on realloc in
// share/smack/lib/stdlib.c.
int main(void) {
  char *p = malloc(4);
  p[0] = 1;
  realloc(p, 0);
  return 0;
}
