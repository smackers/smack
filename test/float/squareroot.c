#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect verified

int main() {
    double a;
    double b;
    
    a = sqrt(4.0);
    b = 2.0;
    
    assert(a == b);
}