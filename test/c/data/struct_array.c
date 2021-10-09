#include "smack.h"
#include <assert.h>

// @expect verified

struct S {
  short a[3];
  short x;
};

struct S s;

int main(void) {
  s.a[s.x] = 1;
  assert(s.a[0] == 1);
  assert(s.a[1] == 0);
  return 0;
}
