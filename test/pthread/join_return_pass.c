
// @expect verified

#include <pthread.h>

int x = 1;

void *t1(void *arg)
{
  x++;
  pthread_exit((void*)5);
}

int main() {

  pthread_t t;

  int a;
  void *ret;

  pthread_create(&t, 0, t1, 0);
  pthread_join(t, &ret);
  assert(x == 2);
  assert((int)ret == 5);
  return 0;
}
