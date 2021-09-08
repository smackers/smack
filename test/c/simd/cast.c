#include "smack.h"
#include <assert.h>
#include <immintrin.h>

// @expect verified

int main(void) {
  long long a = 42;
  __m64 b = (__m64)a;
  assert(b[0] == 42);
  return 0;
}
