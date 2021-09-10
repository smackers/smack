#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect error
// @checkbpl grep -v "call bar"
// @checkout grep "checking_invert_bpl.c(13,3)"

void foo(void) {}

int main(void) {
  foo();
  assert(0);
  return 0;
}
