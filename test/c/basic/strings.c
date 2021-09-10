#include "smack.h"
#include <assert.h>

// @expect verified

const char *s1 = "abcdefg";
const char *s2 = "tuvwxyz";

int main() {
  assert(s1[3] == 'd');
  return 0;
}
