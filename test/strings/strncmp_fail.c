#include <string.h>
#include "smack.h"

// @expect error

int main(void) {
  char *str1 = "aaAA";
  char *str2 = "aBBB";

  assert(strncmp(str1,str2,2) == 0);
  return 0;
}
