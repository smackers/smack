
// @skip
// @expect error

#include <pthread.h>

int x = 1;
int y = 1;

void *t1(void *arg)
{
  x += y;
  x += y;
  x += y;
  x += y;
  x += y;
    
  pthread_exit(0);
}

void *t2(void *arg)
{
  y += x;
  y += x;
  y += x;
  y += x;
  y += x;

  pthread_exit(0);
}

int main() {
  pthread_t tid1, tid2;
  pthread_create(&tid1, 0, t1, 0);
  pthread_create(&tid2, 0, t2, 0);
  assert(x < 144 && y < 144);
}
