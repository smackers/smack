#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect verified

int main(void) {
  char *field = "bbab";
  size_t firstNonB = strspn(field, "b");
  size_t end = strspn(field, "ab");

  assert(firstNonB == 2);
  assert(end == strlen(field));
  return 0;
}
