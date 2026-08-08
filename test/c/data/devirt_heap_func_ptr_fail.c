#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @expect error
// @flag --devirt-mode=all

// This is devirt_heap_func_ptr.c under the default dispatch mode, where a call
// site the points-to analysis cannot resolve is dispatched to every
// address-taken function with a compatible signature.  The uninitialized
// function pointer is therefore taken to reach `bump', and the assertion no
// longer holds.

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
