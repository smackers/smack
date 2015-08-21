/*
 * From svcomp2015
 */

/* Useful
 * Verifies false with u6,s2,tav,si in 45s
 *
 * Fails with SIZE == 10, u11,c2,tav,si:
 *   mcarter@ubuntu:~/projects/smack-project/smack/src/examples/pthreads/svcomp2015$ smackverify.py --verifier corral --verifier-options="/trackAllVars /staticInlining" --unroll 11 --context-switches 2 queue_false-unreach-call.c
 *   Verifying program while tracking: {$CurrAddr, $M.3, $M.0, $M.4, $M.5, $M.6, $M.7, $pthreadStatus, $M.10}
 *   /home/mcarter/projects/smack-project/smack/install/bin/corral: line 2: 27572 Killed                  $CORRAL $@
 *   
 *   SMACK encountered an error when invoking corral. Exiting...
 * 
 * I solved this failure issue - it was due to not enough system memory
 * This benchmark requires over 6GB memory when SIZE==10, u11,c2,tav,si
 * Now, using these setting, verifies false in 180s
 *
 */

// @expect error
// @flag -x=svcomp
// @flag --unroll=6

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <stdio.h>
//#include <assert.h>

#define SIZE	(10)
#define EMPTY	(-1)
#define FULL	(-2)
#define FALSE	(0)
#define TRUE	(1)

typedef struct {
    int element[SIZE];
    int head;
    int tail;
    int amount;
} QType;

pthread_mutex_t m;
int __VERIFIER_nondet_int();
int stored_elements[SIZE];
_Bool enqueue_flag, dequeue_flag;
QType queue;

int init(QType *q) 
{
  q->head=0;
  q->tail=0;
  q->amount=0;
}

int empty(QType * q) 
{
  if (q->head == q->tail) 
  { 
    printf("queue is empty\n");
    return EMPTY;
  }
  else 
    return 0;
}

int full(QType * q) 
{
  if (q->amount == SIZE) 
  {  
	printf("queue is full\n");
	return FULL;
  } 
  else
    return 0;
}

int enqueue(QType *q, int x) 
{
  q->element[q->tail] = x;
  q->amount++;
  if (q->tail == SIZE) 
  {
    q->tail = 1;
  } 
  else 
  {
    q->tail++;
  }

  return 0;
}

int dequeue(QType *q) 
{
  int x;

  x = q->element[q->head];
  q->amount--;
  if (q->head == SIZE) 
  {
    q->head = 1;
  } 
  else 
    q->head++;

  return x;
}

void *t1(void *arg) 
{
  int value, i;

  pthread_mutex_lock(&m);
  value = __VERIFIER_nondet_int();
  if (enqueue(&queue,value)) {
    goto ERROR;
  }

  stored_elements[0]=value;
  if (empty(&queue)) {
    goto ERROR;
  }

  pthread_mutex_unlock(&m);

  for(i=0; i<(SIZE-1); i++)  
  {
    pthread_mutex_lock(&m);
    if (enqueue_flag)
    {
      value = __VERIFIER_nondet_int();
      enqueue(&queue,value);
      stored_elements[i+1]=value;
      enqueue_flag=FALSE;
      dequeue_flag=TRUE;
    }
    pthread_mutex_unlock(&m);
  }	

  return NULL;

  ERROR: __VERIFIER_error();
}

void *t2(void *arg) 
{
  int i;

  for(i=0; i<SIZE; i++)  
  {
    pthread_mutex_lock(&m);
    if (dequeue_flag)
    {
      if (!dequeue(&queue)==stored_elements[i]) {
        ERROR: __VERIFIER_error();
      }
      dequeue_flag=FALSE;
      enqueue_flag=TRUE;
    }
    pthread_mutex_unlock(&m);
  }

  return NULL;
}

int main(void) 
{
  pthread_t id1, id2;

  enqueue_flag=TRUE;
  dequeue_flag=FALSE;

  init(&queue);

  if (!empty(&queue)==EMPTY) {
    ERROR: __VERIFIER_error();
  }


  pthread_mutex_init(&m, 0);

  pthread_create(&id1, NULL, t1, &queue);
  pthread_create(&id2, NULL, t2, &queue);

  pthread_join(id1, NULL);
  pthread_join(id2, NULL);

  return 0;
}

