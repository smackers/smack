// Tests spin_lock_init() function

// @expect error

#include <pthread.h>
#include <smack.h>
#include <spinlock.h>

int z = 1;

void *t1(void *arg) {
  spinlock_t* lock = arg;
  spin_lock(lock);
  z++;
  spin_unlock(lock);
}

int main() {

  spinlock_t lock;
  spin_lock_init(&lock);

  pthread_t tid1;

  pthread_create(&tid1, 0, t1, &lock);
  z++;
  pthread_join(tid1, 0);
  assert(z == 3);
}
