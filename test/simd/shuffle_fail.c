#include <immintrin.h>
#include <smack.h>

// @expect error

int main() {
  __m128i A = _mm_set_epi32(13, 12, 11, 10);
  __m128i B = _mm_set_epi32(23, 22, 21, 20);

  A = _mm_shuffle_epi32(A, 2 * 1 + 3 * 4 + 2 * 16 + 3 * 64);
  B = _mm_shuffle_epi32(B, 2 * 1 + 3 * 4 + 2 * 16 + 3 * 64);

  __m128i C = _mm_blend_epi32(A, B, 0xf0);

  assert(_mm_extract_epi32(C, 0) == 0);
  return 0;
}
