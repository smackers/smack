
#include <stdlib.h>
//#include <stdio.h>
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect verified

int main(void) {
  char word[] = "Hi!!";

  assert(strlen(word) == 4);

  return 0;  
}
