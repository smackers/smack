#include <immintrin.h>
#include <smack.h>

// @expect error

int main(void) {
  __m128i v = {0xff, 0xff};
  assert(v[0] == 0xfe);
  return 0;
}
