#include "smack.h" 
// @flag --bit-precise --clang-options="-fno-strict-aliasing"
// @expect error

int main(void) {
  int i = 2;
  float f = *((float*) &i);
  int i1 = *((int*) &f);
  assert (i != i1);
  return 0;
}
