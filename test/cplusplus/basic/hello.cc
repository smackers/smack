#include <iostream>
#include <smack.h>

// @expect verified

int main() {
  std::cout << "Hello, world!" << std::endl;
  assert(true);
  return 0;
}
