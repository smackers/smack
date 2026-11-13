#include "smack.h"
#include <stdlib.h>

// @flag --check=memleak
// @expect error

int main(void) {
  char *p = malloc(0);
  return 0; // a size-zero block is allocated memory and must be freed
}
