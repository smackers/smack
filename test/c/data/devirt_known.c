#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --devirt-mode=known
// @checkbpl grep -q "devirtbounce_noop"

// The dispatch mode only devirtualizes an indirect call whose targets are
// known.  Calling through `known' reaches `bump', whereas the function pointer
// returned by `unknown_fp' could be anything, so that call becomes a no-op.

typedef void (*fp_t)(int *);

extern fp_t unknown_fp(void);

static void bump(int *p) { *p = 1; }

static fp_t known = bump;

int main(void) {
  int x = 0, y = 0;

  known(&y);

  fp_t f = unknown_fp();
  f(&x);

  assert(y == 1 && x == 0);
  return 0;
}
