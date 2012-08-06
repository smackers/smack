#include <stdlib.h>
#include <stdio.h>

int main() {
  int x = 0;
  char* p = (char*)&x;
  p[2] = 1;

  if (x != 0) {
    printf("Pero %d\n", x);
  }

  {
    int i;
    for (i = 10; i > -1; i--) {
      printf("%d\n", i);
    }
    printf("bla %d\n", i);
  }
  return 0;
}

