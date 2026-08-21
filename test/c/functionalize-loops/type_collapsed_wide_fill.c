#include "smack.h"

// @expect verified
// @checkbpl awk 'index($0,"functional loop summary for fill_words"){found=1} END{exit found}'

union mixed_widths {
  unsigned words[16];
  void *pointers[8];
};

static void fill_words(unsigned *words, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    words[i] = 0;
}

int main(void) {
  union mixed_widths value;
  value.pointers[0] = &value;
  fill_words(value.words, 16);
  return 0;
}
