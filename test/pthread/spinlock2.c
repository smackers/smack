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
  __SMACK_code("assume (forall i:int :: $pthreadStatus[i][0] == $pthread_uninitialized);"); 

  pthread_t tid1, tid2;

  pthread_create(&tid1, NULL, t1, NULL);
  pthread_create(&tid2, NULL, t1, NULL);
  spin_lock(&lock);
  x++;
  spin_unlock(&lock);
  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);
  assert(x == 4);
  

}
