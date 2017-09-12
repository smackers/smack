
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect verified

int main() {
  char *field = "bbab";

  size_t firstNonB = strspn(field,"b");
  size_t end = strspn(field,"ab");

  assert(firstNonB == 2);
  assert(end == strlen(field));

  return 0;
}
