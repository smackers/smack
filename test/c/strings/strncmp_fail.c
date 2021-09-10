#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect error

int main(void) {
  char *str1 = "aaAA";
  char *str2 = "aBBB";

  assert(strncmp(str1, str2, 2) == 0);
  return 0;
}
