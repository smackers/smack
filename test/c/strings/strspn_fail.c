#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect error

int main(void) {
  char *field = "bbcb";
  size_t end = strspn(field, "ab");

  assert(end == strlen(field));
  return 0;
}
