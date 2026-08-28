#include "smack.h"
#include <assert.h>

// @expect error
// @checkbpl grep -F 'call {:cexpr "x->p"} boogie_si_record_i32'
// @checkout grep -F 'x->p = 42'

struct node {
  int p;
};

static void check(struct node *x) { assert(x->p == 0); }

int main(void) {
  struct node n;
  n.p = 42;
  check(&n);
  return 0;
}
