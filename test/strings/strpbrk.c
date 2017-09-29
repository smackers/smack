#include <string.h>
#include "smack.h"

// @flag unroll=5
// @expect verified

int main(void) {
  char *letters = "abcd";
  
  char *fromFirstBorC = strpbrk(letters,"cb");

  assert(strcmp(fromFirstBorC,"bcd") == 0);

  return 0;
}
