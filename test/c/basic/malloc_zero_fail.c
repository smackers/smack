#include "smack.h"
#include <stdlib.h>

// @expect error

int main(void) {
  char *p = malloc(0);
  __VERIFIER_assert(p == 0); // malloc(0) does not return a null pointer
  return 0;
}
