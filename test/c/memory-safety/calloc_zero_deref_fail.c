#include "smack.h"
#include <stdlib.h>

// @expect error

// calloc(0, n) allocates zero bytes (SMACK's calloc may also fail, and a
// null dereference is invalid too).
int main(void) {
  int *p = calloc(0, sizeof(int));
  p[0] = 1;
  free(p);
  return 0;
}
