#include <string.h>
#include "smack.h"

// @expect verified 

int main(void) {
  char *string = "ffef";
  size_t firstE = strcspn(string,"e");

  assert(firstE == 2);
  return 0;
}
