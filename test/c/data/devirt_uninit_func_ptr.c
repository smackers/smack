#include "smack.h"
#include <assert.h>

// @expect verified

// Calling a function pointer that was never initialized is undefined
// behavior, and there is no target to dispatch such a call to.  It must not be
// assumed to reach some function that happens to have a compatible signature,
// whichever dispatch mode is in effect.

typedef void (*fp_t)(int *);

static void bump(int *p) { *p = 1; }

static fp_t known = bump;

int main(void) {
  int x = 0, y = 0;
  fp_t uninitialized;

  known(&y);
  uninitialized(&x);

  assert(y == 1 && x == 0);
  return 0;
}
