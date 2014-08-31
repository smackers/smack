#include <pthread.h>

int x = 1;

void *t1(void *arg)
{
  x++;
  pthread_exit((void*)5);
}

int main() {
  __SMACK_code("assume (forall i:int :: $pthreadStatus[i][0] == $pthread_uninitialized);");
  __SMACK_code("assume (forall i:int :: $ctidToPtid[i] == -1);");

  pthread_t t;

  int a;
  void *ret;

  pthread_create(&t, NULL, t1, NULL);
  pthread_join(t, &ret);
  __SMACK_assert(x == 2);
  __SMACK_assert((int)ret == 6);
  return 0;
}
