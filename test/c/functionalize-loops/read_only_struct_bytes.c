#include <stddef.h>

// @expect verified
// @checkbpl grep -q "functional read-only loop summary for all_zero"

struct record {
  void *pointer;
  size_t length;
};

static int all_zero(const void *data, size_t size) {
  const unsigned char *bytes = data;
  for (size_t i = 0; i < size; ++i)
    if (bytes[i] != 0)
      return 0;
  return 1;
}

int main(void) {
  struct record value;
  return all_zero(&value, sizeof(value));
}
