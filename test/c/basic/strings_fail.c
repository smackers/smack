#include <smack.h>

// @expect error

const char *s1 = "abcdefg";
const char *s2 = "tuvwxyz";

int main() {
  assert(s1[3] == 'f');
  return 0;
}
