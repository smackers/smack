#include "smack.h"
#include <stdlib.h>
#include <string.h>

// @expect verified

// Operations that touch no byte of the block are valid: zero-length memset
// and memcpy in either direction, forming p + 0, comparing the pointer.
int main(void) {
  char *p = malloc(0);
  char *q = malloc(4);
  memset(p, 0, 0);
  memcpy(q, p, 0);
  memcpy(p, q, 0);
  char *end = p + 0;
  if (end == q)
    q[0] = 1;
  free(p);
  free(q);
  return 0;
}
