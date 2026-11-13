#include "smack.h"
#include <stdlib.h>
#include <string.h>

// @expect error

int main(void) {
  char dst[1];
  char *p = malloc(0);
  memcpy(dst, p, 1); // one byte out of a block with none
  free(p);
  return 0;
}
