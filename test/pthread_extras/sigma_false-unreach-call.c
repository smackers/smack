/*
 * From svcomp2015
 */

/* Useful
 * Verifies false with u6,cs2,tav,si in 85s
 */

// @expect error
// @flag -x=svcomp
// @flag --unroll=6

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <stdlib.h>
#include <string.h>

void __VERIFIER_assert(int expression) { if (!expression) { ERROR: __VERIFIER_error();}; return; }

const int SIGMA = 5;

int *array;
int array_index = 0;


void *thread(void * arg)
{
	array[array_index] = 1;
	return 0;
}


int main()
{
	int tid, sum;
	pthread_t *t;

	t = (pthread_t *)malloc(sizeof(pthread_t) * SIGMA);
	array = (int *)malloc(sizeof(int) * SIGMA);

	//__VERIFIER_assume(t);
	//__VERIFIER_assume(array);

	for (tid=0; tid<SIGMA; tid++) {
		pthread_create(&t[tid], 0, thread, 0);
		array_index++;
	}

	for (tid=0; tid<SIGMA; tid++) {
		pthread_join(t[tid], 0);
	}

	for (tid=sum=0; tid<SIGMA; tid++) {
		sum += array[tid];
	}

	__VERIFIER_assert(sum == SIGMA);  // <-- wrong, different threads might use the same array offset when writing

	return 0;
}

