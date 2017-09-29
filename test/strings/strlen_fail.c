
#include <stdlib.h>
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect error

int main(void) {
  char word[] = "Hi";

  assert(strlen(word) == 4);

  return 0;
}
