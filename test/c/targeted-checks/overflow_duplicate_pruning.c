#include "smack.h"

// @flag --check integer-overflow
// @expect verified
// clang-format off
// @checkbpl awk "/call __SMACK_check_overflow/ { n++ } END { exit n == 1 ? 0 : 1 }"
// clang-format on

int main(void) {
  int x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x < 2147483647);
  int y = x + 1;
  int z = x + 1;
  __VERIFIER_assert(y == z);
  return 0;
}
