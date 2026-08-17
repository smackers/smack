// @expect verified
// @checkbpl grep "function \$and.vec.2xi32.*returns (vec.2xi32) { mk.vec.2xi32"

typedef int v2i __attribute__((vector_size(8)));

int main(void) {
  v2i x = {1, 2};
  v2i y = {3, 1};
  v2i z = x & y;
  return z[0];
}
