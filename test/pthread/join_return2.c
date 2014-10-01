#include <pthread.h>

int x = 1;

void *t1(void *arg)
{
  x++;
  pthread_exit((void*)5);
}

void *t2(void *arg)
{
  x++;
  pthread_exit((void*)6);
}

int main() {
  __SMACK_code("assume (forall i:int :: $pthreadStatus[i][0] == $pthread_uninitialized);");

  pthread_t tid1, tid2;

  int a;
  void *ret1, *ret2;

  pthread_create(&tid1, NULL, t1, NULL);
  pthread_create(&tid2, NULL, t2, NULL);
  pthread_join(tid1, &ret1);
  pthread_join(tid2, &ret2);
  __SMACK_assert((int)ret1 == 5);
  __SMACK_assert((int)ret2 == 6);
  return 0;
}
