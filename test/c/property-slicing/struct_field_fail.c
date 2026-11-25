#include "smack.h"
#include <assert.h>

// @expect error

struct S {
  int a;
  int b;
};

int main(void) {
  struct S s;
  s.a = 0;
  s.b = 0;
  s.b = 5;
  assert(s.b != 5);
  return 0;
}
