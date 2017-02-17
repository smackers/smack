
#include <stdlib.h>
//#include <stdio.h>
#include <string.h>
#include "smack.h"

// @expect verified

int main() {
  char word[] = "Hello, world!";

  assert(strlen(word) == 13);

  return 0;  
}
