#include <string.h>
#include "smack.h"

// @expect error 

int main(void) {
  char *letters = "efgh";
  char *fromFirstBorC = strpbrk(letters,"bc");

  assert(fromFirstBorC != 0);
  return 0;
}
