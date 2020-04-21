#include <smack.h>

// @expect verified
// @flag --wrapped-integer-encoding

int main() {
  unsigned x = 2;
  unsigned y = 3;
  assert(x-y > 0);
  return 0;
}
