#include <smack.h>

#define CAS(x,y,z) __atomic_compare_exchange_n(x,&(y),z,true,0,0)

int main() {
	int *x = 0;
  int y = 0;
  int *z = x;
  CAS(&z,x,&y); // if (z == x) z = &y;
  assert(*z == y);
  return 0;
}
