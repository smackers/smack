// This file has a race between caller and callee threads
//  (though no race exists between the two callee threads)
//  when calling the x++ instruction.

#include <pthread.h>

pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

int x = 1;

void *t1(void *arg) {
  pthread_mutex_lock(&lock);
  x++;
  pthread_mutex_unlock(&lock);
}

void *t2(void *arg) {
  pthread_mutex_lock(&lock);
  x++;
  pthread_mutex_unlock(&lock);
}

int main() {
  __SMACK_code("assume (forall i:int :: $pthreadStatus[i][0] == $pthread_uninitialized);"); 

  pthread_t tid1, tid2;

  pthread_create(&tid1, NULL, t1, NULL);
  pthread_create(&tid2, NULL, t2, NULL);
  x++;
  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);
  assert(x == 4);
  

}
