
// @expect error

#include <pthread.h>

int x = 1;

void *t1(void *arg)
{
  x++;
  pthread_exit(0);
}

int main() {

  pthread_t t;

  pthread_create(&t, 0, t1, 0);
  assert(x == 2);
  return 0;
}
