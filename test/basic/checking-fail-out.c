#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect error
// @checkbpl grep "call foo"
// @checkout grep -v "CALL bar"

void foo(void) {

}

int main(void) {
  foo();
  assert(0);
  return 0;
}
