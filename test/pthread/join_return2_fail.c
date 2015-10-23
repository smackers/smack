// Ensures return values from multiple threads can be 
// held simultaneously.


// @expect error

#include <pthread.h>
#include <smack.h>

int x = 1;

void *t1(void *arg) {
  x++;
  pthread_exit((void*)5);
}

void *t2(void *arg) {
  x++;
  pthread_exit((void*)6);
}

int main() {

  pthread_t tid1, tid2;

  int a;
  void *ret1, *ret2;

  pthread_create(&tid1, 0, t1, 0);
  pthread_create(&tid2, 0, t2, 0);
  pthread_join(tid1, &ret1);
  pthread_join(tid2, &ret2);
  assert((int)ret1 == 5);
  assert((int)ret2 == (int)ret1);
  return 0;
}
