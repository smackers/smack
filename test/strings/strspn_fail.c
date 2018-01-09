#include <string.h>
#include "smack.h"

// @expect error 

int main(void) {
  char *field = "bbcb";
  size_t end = strspn(field,"ab");

  assert(end == strlen(field));
  return 0;
}
