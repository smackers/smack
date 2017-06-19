#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect error
// @checkbpl grep -v "call bar"
// @checkout grep "checking_invert_bpl.c(11,1)"

void foo(void) {

}

int main(void) {
  foo();
  assert(0);
  return 0;
}
