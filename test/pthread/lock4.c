#include <pthread.h>

pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

int x = 1;

void *t1(void *arg) {
  pthread_mutex_lock(&lock);
  x++;
  pthread_mutex_unlock(&lock);
}

int main() {
  __SMACK_code("assume (forall i:int :: $pthreadStatus[i][0] == $pthread_uninitialized);"); 

  pthread_t tid[5];

  pthread_create(&tid[0], NULL, t1, NULL);
  pthread_create(&tid[1], NULL, t1, NULL);
  pthread_create(&tid[2], NULL, t1, NULL);
  pthread_create(&tid[3], NULL, t1, NULL);
  //pthread_create(&tid[4], NULL, t1, NULL);
  pthread_mutex_lock(&lock);
  x++;
  pthread_mutex_unlock(&lock);
  pthread_join(tid[0], NULL);
  pthread_join(tid[1], NULL);
  pthread_join(tid[2], NULL);
  pthread_join(tid[3], NULL);
  //pthread_join(tid[4], NULL);
  __SMACK_assert(x == 6);
  

}
