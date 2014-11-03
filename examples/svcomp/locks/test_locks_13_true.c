#include "smack.h"
extern int __VERIFIER_nondet_int();
int main()
{
    int p1 = __VERIFIER_nondet_int();  // condition variable
    int lk1; // lock variable

    int p2 = __VERIFIER_nondet_int();  // condition variable
    int lk2; // lock variable

    int p3 = __VERIFIER_nondet_int();  // condition variable
    int lk3; // lock variable

    int p4 = __VERIFIER_nondet_int();  // condition variable
    int lk4; // lock variable

    int p5 = __VERIFIER_nondet_int();  // condition variable
    int lk5; // lock variable

    int p6 = __VERIFIER_nondet_int();  // condition variable
    int lk6; // lock variable

    int p7 = __VERIFIER_nondet_int();  // condition variable
    int lk7; // lock variable

    int p8 = __VERIFIER_nondet_int();  // condition variable
    int lk8; // lock variable

    int p9 = __VERIFIER_nondet_int();  // condition variable
    int lk9; // lock variable

    int p10 = __VERIFIER_nondet_int();  // condition variable
    int lk10; // lock variable

    int p11 = __VERIFIER_nondet_int();  // condition variable
    int lk11; // lock variable

    int p12 = __VERIFIER_nondet_int();  // condition variable
    int lk12; // lock variable

    int p13 = __VERIFIER_nondet_int();  // condition variable
    int lk13; // lock variable


    int cond;

    while(1) {
        cond = __VERIFIER_nondet_int();
        if (cond == 0) {
            goto out;
        } else {}
        lk1 = 0; // initially lock is open

        lk2 = 0; // initially lock is open

        lk3 = 0; // initially lock is open

        lk4 = 0; // initially lock is open

        lk5 = 0; // initially lock is open

        lk6 = 0; // initially lock is open

        lk7 = 0; // initially lock is open

        lk8 = 0; // initially lock is open

        lk9 = 0; // initially lock is open

        lk10 = 0; // initially lock is open

        lk11 = 0; // initially lock is open

        lk12 = 0; // initially lock is open

        lk13 = 0; // initially lock is open


    // lock phase
        if (p1 != 0) {
            lk1 = 1; // acquire lock
        } else {}

        if (p2 != 0) {
            lk2 = 1; // acquire lock
        } else {}

        if (p3 != 0) {
            lk3 = 1; // acquire lock
        } else {}

        if (p4 != 0) {
            lk4 = 1; // acquire lock
        } else {}

        if (p5 != 0) {
            lk5 = 1; // acquire lock
        } else {}

        if (p6 != 0) {
            lk6 = 1; // acquire lock
        } else {}

        if (p7 != 0) {
            lk7 = 1; // acquire lock
        } else {}

        if (p8 != 0) {
            lk8 = 1; // acquire lock
        } else {}

        if (p9 != 0) {
            lk9 = 1; // acquire lock
        } else {}

        if (p10 != 0) {
            lk10 = 1; // acquire lock
        } else {}

        if (p11 != 0) {
            lk11 = 1; // acquire lock
        } else {}

        if (p12 != 0) {
            lk12 = 1; // acquire lock
        } else {}

        if (p13 != 0) {
            lk13 = 1; // acquire lock
        } else {}


    // unlock phase
        if (p1 != 0) {
            if (lk1 != 1) goto ERROR; // assertion failure
            lk1 = 0;
        } else {}

        if (p2 != 0) {
            if (lk2 != 1) goto ERROR; // assertion failure
            lk2 = 0;
        } else {}

        if (p3 != 0) {
            if (lk3 != 1) goto ERROR; // assertion failure
            lk3 = 0;
        } else {}

        if (p4 != 0) {
            if (lk4 != 1) goto ERROR; // assertion failure
            lk4 = 0;
        } else {}

        if (p5 != 0) {
            if (lk5 != 1) goto ERROR; // assertion failure
            lk5 = 0;
        } else {}

        if (p6 != 0) {
            if (lk6 != 1) goto ERROR; // assertion failure
            lk6 = 0;
        } else {}

        if (p7 != 0) {
            if (lk7 != 1) goto ERROR; // assertion failure
            lk7 = 0;
        } else {}

        if (p8 != 0) {
            if (lk8 != 1) goto ERROR; // assertion failure
            lk8 = 0;
        } else {}

        if (p9 != 0) {
            if (lk9 != 1) goto ERROR; // assertion failure
            lk9 = 0;
        } else {}

        if (p10 != 0) {
            if (lk10 != 1) goto ERROR; // assertion failure
            lk10 = 0;
        } else {}

        if (p11 != 0) {
            if (lk11 != 1) goto ERROR; // assertion failure
            lk11 = 0;
        } else {}

        if (p12 != 0) {
            if (lk12 != 1) goto ERROR; // assertion failure
            lk12 = 0;
        } else {}

        if (p13 != 0) {
            if (lk13 != 1) goto ERROR; // assertion failure
            lk13 = 0;
        } else {}

    }
  out:
    return 0;
  ERROR: assert(0);
    return 0;  
}

