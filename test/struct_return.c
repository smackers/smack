#include "smack.h"

struct a {
  long i;
  long j;
};

struct a foo(struct a bar) {
  bar.i = 10;
  bar.j = 20;
  return bar;
}

int main(void) {
  struct a x;
  x = foo(x);
  __SMACK_assert(x.j == 20);
  return 0;
}

