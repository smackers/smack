
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect error

int main() {
  char *str1 = "aaAA";
  char *str2 = "aBBB";

  assert(strncmp(str1,str2,2) == 0);
  return 0;
}
