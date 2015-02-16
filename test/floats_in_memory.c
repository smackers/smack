#include <smack.h>

void ff1(float f);
void ff2(float *f1, float *f2) {
  *f1 = *f2;
}

int main() {
  float f1;
  float f2 = 0.0;
  float f3 = 1.0;

  ff1(f1);
  ff1(f2);
  ff2(&f2,&f3);

  assert(f2 == f3);

  return 0;
}
