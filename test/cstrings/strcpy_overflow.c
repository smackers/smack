
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @flag --memory-safety
// @expect error

int main() {
  const char *sentence = "long";
  char container[2];
  
  strcpy(container,sentence); // buffer overflow!
  return 0;
}

