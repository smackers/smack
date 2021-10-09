#include "smack.h"
#include <assert.h>
#include <pthread.h>
#include <stdlib.h>

// @expect error

#define TRUE 1
#define FALSE 0

// Bank Account Example

// Account structure
typedef struct {
  int balance;
  int withdrawn;
  pthread_mutex_t lock;
} ACCOUNT, *PACCOUNT;

// Account global
PACCOUNT acc;

// Create and initialize account
PACCOUNT create(int b) {
  PACCOUNT acc = (PACCOUNT)malloc(sizeof(ACCOUNT));
  acc->balance = b;
  acc->withdrawn = FALSE;
  pthread_mutex_init(&acc->lock, 0);
  return acc;
}

// Read account balance
int read() { return acc->balance; }

void *deposit(void *arg) {
  int *n = (int *)arg;
  pthread_mutex_lock(&acc->lock);
  acc->balance = acc->balance + *n;
  pthread_mutex_unlock(&acc->lock);
  return 0;
}

// Withdraw if there is enough funds in the account
void *withdraw(void *arg) {
  int *n = (int *)arg;
  int r;
  r = read();
  if (r >= *n) {
    pthread_mutex_lock(&acc->lock);
    acc->balance = r - *n;
    pthread_mutex_unlock(&acc->lock);
    acc->withdrawn = TRUE;
    return 0;
  }
  acc->withdrawn = FALSE;
  return 0;
}

int main(void) {
  pthread_t tid1, tid2;
  int x, y, z;

  // Initialization
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();
  acc = create(x);

  // Threads
  pthread_create(&tid1, 0, deposit, &y);
  pthread_create(&tid2, 0, withdraw, &z);

  pthread_join(tid1, 0);
  pthread_join(tid2, 0);

  assert(!acc->withdrawn || read() == x + y - z);
  return 0;
}
