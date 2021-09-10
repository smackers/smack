#include "smack.h"
#include <assert.h>

// @expect error

void foo(int *p) { assert(p[-1] != 0); }

int main(void) {
  int a[3] = {0};
  foo(&a[1]);
  return 0;
}
