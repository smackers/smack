
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect error 

int main() {
  char *field = "bbcb";

  size_t end = strspn(field,"ab");

  assert(end == strlen(field));

  return 0;
}
