#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect error

int main(void) {
  char word1[] = "Test memcmp";
  char word2[] = "Test memcpy";
  char word3[] = "Test memcmp";
  int result1, result2;

  result1 = memcmp(word1, word2, 11);
  result2 = memcmp(word1, word3, 11);
  assert(result1 >= 0 || result2 != 0);

  return 0;
}
