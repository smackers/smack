#include "smack.h"
#include <assert.h>

// @expect error

int foo(int x) {
  int y = __VERIFIER_nondet_int();
  __SMACK_top_decl("function FOO(x: int): int;");
  __SMACK_code("@ := FOO(@);", y, x);
  return y;
}

int main(void) {
  int x = foo(42);
  int y = foo(43);
  assert(x == y);

  return 0;
}
