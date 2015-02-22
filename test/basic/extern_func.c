#include "smack.h"

// @flag --unroll=2
// @expect verified

extern int foo(int x);

int main(void) {
  int a;
  a = foo(10);
  return a;
}

