#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect verified
// @flag --devirt-mode=known
// @checkbpl grep -q "devirtbounce_noop"

// The function pointer is read out of heap memory that was never initialized.
// Its sea-dsa node refers to the allocation rather than to any global, so the
// targets are unknown and the call becomes a no-op.  See
// devirt_heap_func_ptr_fail.c for what the default dispatch mode makes of the
// very same program.

typedef void (*fp_t)(int *);

struct handler {
  fp_t run;
};

static void bump(int *p) { *p = 1; }

static fp_t known = bump;

int main(void) {
  int x = 0, y = 0;
  struct handler *h = (struct handler *)malloc(sizeof(struct handler));

  known(&y);
  h->run(&x);

  assert(y == 1 && x == 0);
  free(h);
  return 0;
}
