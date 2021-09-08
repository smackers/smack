#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect error
// @checkbpl grep "call foo"
// @checkout grep -v "checking_invert_out.c(10,1)"

void foo(void) {}

int main(void) {
  foo();
  assert(0);
  return 0;
}
