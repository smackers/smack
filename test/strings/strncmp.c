
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect verified

int main(void) {
  char *str1 = "aaAA";
  char *str2 = "aaBB";

  assert(strncmp(str1,str2,2) == 0);
  assert(strncmp(str1,str2,3) < 0);
  return 0;
}
