#include "smack.h"
#include <assert.h>

// @expect error
// @flag --devirt-mode=known

// A call that is turned into a no-op returns an unconstrained value, so
// nothing may be assumed about the result of calling an unknown function
// pointer.

typedef int (*fp_t)(int);

extern fp_t unknown_fp(void);

static int incr(int x) { return x + 1; }

static fp_t known = incr;

int main(void) {
  fp_t f = unknown_fp();

  assert(f(41) == known(41));
  return 0;
}
