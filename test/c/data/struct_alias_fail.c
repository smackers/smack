#include "smack.h"
#include <assert.h>

// @expect error

struct S {
  int w;
};

struct T {
  int x;
  struct S y;
  struct S z;
};

void f(struct S *state) { state->w = 0; }

void g(struct S *state) { state->w = 1; }

int main(void) {
  struct T t;

  f(&t.y);
  f(&t.z);
  g(&t.z);

  assert(t.y.w == 1);

  return 0;
}
