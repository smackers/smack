#include "smack.h"

// @expect verified

extern int foo(int x);

int main(void) {
  int a;
  a = foo(10);
  return a;
}
