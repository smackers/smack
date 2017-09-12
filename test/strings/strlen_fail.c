
#include <stdlib.h>
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect error

int main() {
  char word[] = "Hi";

  assert(strlen(word) == 4);

  return 0;
}
