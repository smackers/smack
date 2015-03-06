#include "smack.h"

// @expect verified

void __SMACK_init_func_test() {
  assert(1);
}

void __SMACK_init_func_test2() {
  assert(2);
}

void main() {
  int a = 1;
  assert(a==1);
}
