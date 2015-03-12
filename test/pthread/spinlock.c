#include <pthread.h>
#include <spinlock.h>

int z = 1;

void *t1(void *arg) {
  spinlock_t* lock = arg;
  spin_lock(lock);
  z++;
  spin_unlock(lock);
}

int main() {
  __SMACK_code("assume (forall i:int :: $pthreadStatus[i][0] == $pthread_uninitialized);"); 

  spinlock_t lock;
  spin_lock_init(&lock);

  pthread_t tid1;

  pthread_create(&tid1, NULL, t1, &lock);
  spin_lock(&lock);
  z++;
  spin_unlock(&lock);
  pthread_join(tid1, NULL);
  assert(z == 3);
  

}
