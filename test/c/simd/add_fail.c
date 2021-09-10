#include "smack.h"
#include <assert.h>
#include <immintrin.h>

// @expect error

int main(void) {
  __m128i a = _mm_set_epi64x(1, 2);
  __m128i b = _mm_set_epi64x(10, 10);
  __m128i c = _mm_add_epi64(a, b);
  assert(c[0] != 12);
  return 0;
}
