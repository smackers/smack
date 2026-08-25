#include "smack.h"
#include <stddef.h>
// @flag --sign-analysis --unroll=8 --loop-limit=8
// @flag --clang-options=-fno-sanitize=unsigned-integer-overflow
// @expect verified
int main(void) {
  size_t n = 5, count = 0;
  for (size_t i = n; i > 0; i--)
    count++;
  __VERIFIER_assert(count == 5);
  return 0;
}
