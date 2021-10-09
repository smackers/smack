#include "smack.h"
#include <assert.h>
#include <immintrin.h>

// @expect verified

int main(void) {
  __m128i v = {0xff, 0xff};
  assert(v[0] == 0xff);
  return 0;
}
