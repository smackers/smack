#include <pthread.h>

int x = 1;

void *t1(void *arg)
{
  x++;
  pthread_exit(NULL);
}

int main() {
  __SMACK_code("assume (forall i:int :: $pthreadStatus[i][0] == $pthread_uninitialized);");

  pthread_t t;

  pthread_create(&t, NULL, t1, NULL);
  assert(x == 2);
  return 0;
}
