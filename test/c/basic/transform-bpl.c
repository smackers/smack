#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified
// @flag --transform-bpl "sed 's/\(call .*\) bar/\1 foo/'"

int foo(void) { return 0; }

int bar(void) { return 1; }

int main(void) {
  int x = foo();
  int y = bar();
  assert(y == 0);
  return 0;
}
