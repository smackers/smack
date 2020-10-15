#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect error

int main(void) {
  unsigned long long x = 0;
  memset(&x, 1, sizeof(x));
  assert(x == 1);
  return 0;
}
