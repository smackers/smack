
#include <string.h>
#include "smack.h"

// @flag --unroll=10
// @expect error 

int main() {
  char brick[10];
  strcpy(brick,"brick");
  
  char *glue = "glu!";

  char *modernart = strcat(brick,glue);

  assert(strcmp(modernart,"brickglu") == 0);

  return 0;
}
