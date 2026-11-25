#include "smack.h"
#include <assert.h>

// @expect error

int main(void) {
  int a[4];
  a[0] = 0;
  a[2] = 9;
  assert(a[2] != 9);
  return 0;
}
