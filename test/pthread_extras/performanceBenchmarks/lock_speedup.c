
// @skip

#include <pthread.h>
#include <smack.h>

pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

int x = 1;

void *t1(void *arg) {
  pthread_mutex_lock(&lock);
  x++;
  x++;
  x++;
  x++;
  x++;

  x++;
  x++;
  x++;
  x++;
  x++;
  pthread_mutex_unlock(&lock);
}

int main() {

  pthread_t tid1, tid2, tid3;

  pthread_create(&tid1, 0, t1, 0);
  pthread_create(&tid2, 0, t1, 0);
  pthread_create(&tid3, 0, t1, 0);
  pthread_join(tid1, 0);
  pthread_join(tid2, 0);
  pthread_join(tid3, 0);
  assert(x == 31);
  

}
