#include "smack.h"
#include <assert.h>

// @flag --clang-options=-O1
// @expect verified

typedef struct {
  int a;
  long b;
} S;

S foo() {
  S x = {1, 2L};
  assert(1);
  return x;
}

int main() {
  S y = foo();
  assert(y.a == 1);
  return 0;
}
