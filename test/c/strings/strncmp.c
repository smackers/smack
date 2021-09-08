#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect verified

int main(void) {
  char *str1 = "aaAA";
  char *str2 = "aaBB";

  assert(strncmp(str1, str2, 2) == 0);
  assert(strncmp(str1, str2, 3) < 0);
  return 0;
}
