#include <pthread.h>

pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

int x = 1;

void *t1(void *arg) {
  pthread_mutex_lock(&lock);
  x++;
  pthread_mutex_unlock(&lock);
}

int main() {

  pthread_t tid[5];

  pthread_create(&tid[0], 0, t1, 0);
  pthread_create(&tid[1], 0, t1, 0);
  pthread_create(&tid[2], 0, t1, 0);
  pthread_create(&tid[3], 0, t1, 0);
  //pthread_create(&tid[4], 0, t1, 0);
  pthread_mutex_lock(&lock);
  x++;
  pthread_mutex_unlock(&lock);
  pthread_join(tid[0], 0);
  pthread_join(tid[1], 0);
  pthread_join(tid[2], 0);
  pthread_join(tid[3], 0);
  //pthread_join(tid[4], 0);
  assert(x == 6);
  

}
