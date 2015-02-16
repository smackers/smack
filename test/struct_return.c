#include "smack.h"
#include <inttypes.h>

struct a {
  int64_t i;
  int64_t j;
};

struct a foo(struct a bar) {
  bar.i = 10;
  bar.j = 20;
  return bar;
}

int main(void) {
  struct a x;
  x = foo(x);
  assert(x.j == 20);
  return 0;
}

