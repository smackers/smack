#include "smack-defs.h"
#include <limits.h>
int main()
{
	int v = __SMACK_nondet();           	// we want to find the absolute value of v
	unsigned int r;       			// the result goes here 
	int mask;
	assume(v < 0);
	mask = v >> sizeof(int) * CHAR_BIT - 1;

	r = (v + mask) ^ mask;
	assert(r == v);
}
