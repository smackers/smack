#include "smack.h"

// @expect verified

int x;
int *p = &x;

int main(void) { return *p; }
