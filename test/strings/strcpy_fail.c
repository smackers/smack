#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect verified

int main(void) {
  const char *word = "made";
  char container[5];
  
  strcpy(container,word);
  assert(strcmp(container,"made") != 0);
  return 0;
}

