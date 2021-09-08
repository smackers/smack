#include "smack.h"
#include <assert.h>

// @flag --integer-encoding=bit-vector --clang-options="-fno-strict-aliasing"
// @expect verified

int main(void) {
  int i = 2;
  float f = *((float *)&i);
  int i1 = *((int *)&f);
  assert(i == i1);
  return 0;
}
