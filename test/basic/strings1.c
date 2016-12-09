#include <smack.h>

// @expect verified

int main() {
  char *s1 = "abcdefg";
  assert(s1[3] == 'd');
  return 0;
}

