#include "smack.h"
#include <stdlib.h>
#include <string.h>

// @expect error

// A one-byte memset touches the block; a library call is checked like a
// direct access.
int main(void) {
  char *p = malloc(0);
  memset(p, 0, 1);
  free(p);
  return 0;
}
