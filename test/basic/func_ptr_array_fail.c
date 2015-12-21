#include "smack.h"

// @expect error

void (*fptrs[2])();

void func2() {
  assert(0 != 0);
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
  return 0;
}
