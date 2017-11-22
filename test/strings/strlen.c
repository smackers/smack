#include <stdlib.h>
#include <string.h>
#include "smack.h"

// @expect verified

int main(void) {
  char word[] = "Hi!!";

  assert(strlen(word) == 4);
  return 0;  
}
