
#include <strings.h>
#include "smack.h"

// @expect verified

int main() {
  const char *word = "Roof";
  char container[10];
  
  strcpy(container,word);
  assert(strlen(container) == 4);
  assert(strcmp(container,word) == 0);
  return 0;
}

