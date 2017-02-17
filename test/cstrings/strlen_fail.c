
#include <stdlib.h>
#include <string.h>
#include "smack.h"

// @expect error

int main() {
  char word[] = "Hello, World";

  assert(strlen(word) == 14); // really is 12

  return 0;
}
