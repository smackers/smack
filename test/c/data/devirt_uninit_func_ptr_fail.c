#include "smack.h"
#include <stdlib.h>

// @expect error
// @flag --devirt-mode=known
// @flag --check memory-safety

// Turning a call with unknown targets into a no-op drops whatever that call
// would have done, but it must not make the rest of the program look safe: the
// use after free below still has to be reported.

typedef void (*fp_t)(void);

int main(void) {
  int *p = (int *)malloc(sizeof(int));
  fp_t uninitialized;

  free(p);
  uninitialized();
  *p = 1;

  return 0;
}
