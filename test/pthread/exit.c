#include <pthread.h>

int x = 1;

void *t1(void *arg)
{
  x++;
  if(x == 2)
    pthread_exit((void*)5);

  //Should never run this line, since called pthread_exit
  pthread_exit((void*)6);
}

int main() {
  __SMACK_code("assume (forall i:int :: $pthreadStatus[i][0] == $pthread_uninitialized);");

  pthread_t t;

  int a;
  void *ret;

  pthread_create(&t, NULL, t1, NULL);
  pthread_join(t, &ret);
  __SMACK_assert((int)ret == 5);
  return 0;
}
