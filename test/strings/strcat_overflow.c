
#include <string.h>
#include "smack.h"

// @flag --unroll=13
// @flag --memory-safety
// @expect error

int main() {
  char notLong[5] = "Some";

  char *moreText = "...";

  char *overflowed = strcat(notLong,moreText);

  assert(strcmp(overflowed,"Some...") == 0);

  return 0;  
}

