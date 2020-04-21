#include <smack.h>

// @expect error
// @flag --wrapped-integer-encoding

int main() {
  unsigned x = 2;
  unsigned y = 3;
  assert(x-y < 1);
  return 0;
}
