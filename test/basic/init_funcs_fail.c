#include "smack.h"

// @expect error

void __SMACK_init_func_test() {
  assert(0);
}

void main() {
  int a = 1;
  assert(a==1);
}
