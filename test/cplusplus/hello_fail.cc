#include <iostream>
#include <smack.h>

// @expect error

int main() {
  std::cout << "Hello, world!" << std::endl;
  assert(false);
  return 0;
}
