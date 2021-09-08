#include "smack.h"
#include <assert.h>
#include <stdint.h>

// @expect error
// @flag --unroll=3

uint32_t ctlz32(uint32_t x) {
  uint32_t n = 32;
  uint32_t y;

  y = x >> 16;
  if (y != 0) {
    n = n - 16;
    x = y;
  }
  y = x >> 8;
  if (y != 0) {
    n = n - 8;
    x = y;
  }
  y = x >> 4;
  if (y != 0) {
    n = n - 4;
    x = y;
  }
  y = x >> 2;
  if (y != 0) {
    n = n - 2;
    x = y;
  }
  y = x >> 1;
  if (y != 0)
    return n - 2;
  return n - x;
}

int main(void) {
  uint32_t x32 = 1;
  uint32_t leadingZeros = 0;
  for (int i = 0; i < 2; ++i) {
    leadingZeros = __builtin_ctz(x32);
    x32--;
  }
  assert(leadingZeros <= 32);
  return 0;
}
