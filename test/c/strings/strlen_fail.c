#include "smack.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

// @expect error

int main(void) {
  char word[] = "Hi";

  assert(strlen(word) == 4);
  return 0;
}
