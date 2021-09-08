#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect error

int main(void) {
  char *string = "ffff";
  size_t firstE = strcspn(string, "f");

  assert(firstE == 5);
  return 0;
}
