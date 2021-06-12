#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect verified

int main(void) {
  char word1[] = "Test memcmp";
  char word2[] = "Test memcmp";
  char word3[] = "Test memcpy";
  int result;

  result = memcmp(word1, word2, 11);
  assert(result == 0);
  result = memcmp(word1, word3, 11);
  assert(result < 0);
  result = memcmp(word1, word3, 8);
  assert(result == 0);

  return 0;
}
