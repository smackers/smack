/* C source */
#include <stdlib.h>
int* x;
void init() {
  x = calloc(100*sizeof(int), 0);
}
int* get_x() {
  return x;
}
const int* get_elem(size_t i) {
  return &x[i];
}
void set_elem(size_t i, int a) {
  x[i] = a;
}
void finalize() {
  free(x);
  x = NULL;
}
