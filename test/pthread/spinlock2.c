
// @expect verified

#include <pthread.h>
#include <spinlock.h>

DEFINE_SPINLOCK(lock);

int x = 1;

void *t1(void *arg) {
  spin_lock(&lock);
  x++;
  spin_unlock(&lock);
}

int main() {

  pthread_t tid1, tid2;

  pthread_create(&tid1, 0, t1, 0);
  pthread_create(&tid2, 0, t1, 0);
  spin_lock(&lock);
  x++;
  spin_unlock(&lock);
  pthread_join(tid1, 0);
  pthread_join(tid2, 0);
  assert(x == 4);
  

}
