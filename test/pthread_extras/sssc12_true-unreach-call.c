/*
 * From svcomp2015
 */

/* Useful
 * Verifies false with u11,s2,tav,si in 54s
 */

// @expect verified
// @flag -x=svcomp

// Source: Alejandro Sanchez, Sriram Sankaranarayanan, Cesar Sanchez, Bor-Yuh
// Evan Chang: "Invariant Generation for Paramterized Systems using
// Self-Reflection", SAS 2012

#include <pthread.h>
#include <smack.h>
#include "assert.h"

void __VERIFIER_assert(int expression) { if (!expression) { ERROR: __VERIFIER_error();}; return; }

int *data;
volatile int len;
volatile int next;
pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

void* thr(void* arg) {
    int c, end;
    c = 0;
    end = 0;
    
    pthread_mutex_lock(&lock);
    if (next + 10 <= len) {
	c = next;
	next = end = next + 10;
    }
    pthread_mutex_unlock(&lock);
    while (c < end) {
	__VERIFIER_assert(0 <= c && c < len);
	data[c] = 0;
	c = c + 1;
    }
}

void main() {
    pthread_t t;
    next = 0;
    len = __VERIFIER_nondet_int();
    __VERIFIER_assume(len > 0);
    data = malloc(sizeof(int) * len);
    while(1) {
	pthread_create(&t, 0, thr, 0);
    }
}
