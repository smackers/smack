#include "smack.h"
#include <assert.h>

// @expect verified

struct S {
  int x;
  int y;
};

int eq(struct S p1, struct S p2) { return p1.y == p2.y; }

int main(void) {
  struct S p = {0, 0};
  struct S q = {1, 1};
  p = q;
  assert(p.y == q.y);
  assert(eq(p, q));
  return 0;
}
