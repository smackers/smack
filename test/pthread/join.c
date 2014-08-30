#include <pthread.h>

int x = 1;

void *t1(void *arg)
{
  x++;
  pthread_exit(NULL);
}

int main() {
  __SMACK_code("assume (forall i:int :: $threadStatus[i] == $pthread_uninitialized);");

  pthread_t t;

  pthread_create(&t, NULL, t1, NULL);
  pthread_join(t, NULL);
  __SMACK_assert(x == 2);
  return 0;
}
