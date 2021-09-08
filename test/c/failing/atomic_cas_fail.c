#include "smack.h"
#include <assert.h>
#include <stdbool.h>

// @expect error

#define CAS(x, y, z) __atomic_compare_exchange_n(x, &(y), z, true, 0, 0)

int main(void) {
  int *x = 0;
  int y = 0;
  int *z = x;
  CAS(&z, x, &y); // if (z == x) z = &y;
  assert(*z != y);
  return 0;
}
