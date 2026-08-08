#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --devirt-mode=known
// @checkbpl grep -q "devirtbounce_noop"

// A null function pointer is a constant, but it is not a function, so the call
// through it has no target and becomes a no-op.  The call through `known' next
// to it still gets dispatched.

typedef void (*fp_t)(int *);

static void bump(int *p) { *p = 1; }

static fp_t known = bump;

int main(void) {
  int x = 0, y = 0;
  fp_t null_ptr = 0;

  known(&y);
  null_ptr(&x);

  assert(y == 1 && x == 0);
  return 0;
}
