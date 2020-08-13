#include "smack.h"

// @expect error
// @flag --unroll=7

int func(int a) {
  int ans = 0;

  if (a < 5) {
    goto exit;
  }

  for (int i = 0; i < a; i++)
    ans++;

exit:
  ans++;
  return ans;
}

int main(void) {
  int i = func(2);
  int j = func(6);

  return i + j;
}


