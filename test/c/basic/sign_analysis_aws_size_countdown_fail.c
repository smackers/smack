#include "smack.h"
#include <stddef.h>
// @flag --sign-analysis
// @flag
// --clang-options=-fno-sanitize=signed-integer-overflow,unsigned-integer-overflow
// @expect error
int main(void) {
  size_t n = 5, count = 0;
  for (size_t i = n; i > 0; i--)
    count++;
  __VERIFIER_assert(count == 4);
  return 0;
}
