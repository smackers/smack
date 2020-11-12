#include "smack.h"
#include <stdint.h>

// @expect error

uint8_t ctpop8(uint8_t x) {
  uint8_t result = 0;
  result += x % 2;
  x /= 2;
  result += x % 2;
  x /= 2;
  result += x % 2;
  x /= 2;
  result += x % 2;
  x /= 2;
  result += x % 2;
  x /= 2;
  result += x % 2;
  x /= 2;
  result += x % 2;
  x /= 2;
  result += x % 2;
  return result;
}

int main(void) {
  uint8_t x = __VERIFIER_nondet_unsigned_char();
  __VERIFIER_assume(x < 32);
  assert(__builtin_popcount(x) != ctpop8(x));
  return 0;
}
