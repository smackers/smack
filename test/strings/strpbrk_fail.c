
#include <string.h>
#include "smack.h"

// @flag unroll=5
// @expect error 

int main(void) {
  char *letters = "efgh";
  
  char *fromFirstBorC = strpbrk(letters,"bc");

  assert(fromFirstBorC != 0);

  return 0;
}
