#include "smack.h"

// @expect verified

void (*fptrs[2])();
int g;

void func2() {
  g = 1;
}

void add_func(void (*f)()) {
  fptrs[1] = f;
}

void func1() {
  add_func(func2);
}

int main(void) {
  fptrs[0] = func1;
  fptrs[0]();
  fptrs[1]();
  assert (g == 1);
  return 0;
}
