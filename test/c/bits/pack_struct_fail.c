#include "smack.h"
#include <assert.h>
#include <stdbool.h>

// @expect error

struct S {
  int x;
  int y;
};

// Clang packs each argument as a 64-bit integer,
// which introduces false alarms without
// the `--integer-encoding=bit-vector` flag
bool eq(struct S p1, struct S p2) { return p1.y == p2.y; }

int main(void) {
  struct S p;
  struct S q;

  p = q;
  assert(!eq(p, q));

  return 0;
}
