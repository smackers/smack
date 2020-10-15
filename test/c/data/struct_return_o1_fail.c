#include "smack.h"
#include <assert.h>

// @expect error
// @flag --clang-options=-O1

int *A;

typedef struct {
  int *a;
  long b;
} S;

S foo() {
  S x = {A, 2L};
  assert(1);
  return x;
}

int main(void) {
  int a = 1;
  A = &a;
  S y = foo();
  assert(*(y.a) == 3);
  return 0;
}
