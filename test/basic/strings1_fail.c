#include <smack.h>

// @expect error

int main() {
  char *s1 = "abcdefg";
  assert(s1[3] == 'f');
  return 0;
}

