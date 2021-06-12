#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect error

int main(void) {
  char brick[4];
  strcpy(brick, "bl");
  char *glue = "u!";
  char *modernart = strcat(brick, glue);

  assert(strcmp(modernart, "blue") == 0);
  return 0;
}
