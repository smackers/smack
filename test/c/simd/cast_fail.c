#include <immintrin.h>
#include <smack.h>

// @expect error

int main(void) {
  long long a = 42;
  __m64 b = (__m64)a;
  assert(b[0] == 41);
  return 0;
}
