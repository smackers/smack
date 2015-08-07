#include <smack.h>

// @flag --unroll=2
// @expect verified

int main() {
  int x = __SMACK_nondet();
  assert(x < x + 599147937792);
  return 0;
}