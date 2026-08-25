// This file is distributed under the MIT License. See LICENSE for details.
// @expect verified
// clang-format off
// @flag --sign-analysis --clang-options=-fno-sanitize=signed-integer-overflow,unsigned-integer-overflow
// @checkbpl grep -F '$add.i32($i0, $sub.i32(0, 3))'
// @checkbpl grep -F '$add.i32($i0, $sub.i32(0, 2))'
// @checkbpl grep -F '$sub.i32($i0, $sub.i32(0, 3))'
// @checkbpl grep -F '$sub.i32($i0, $sub.i32(0, 2))'
// @checkbpl grep -F '$mul.i32($i0, $sub.i32(0, 3))'
// @checkbpl grep -F '$mul.i32($i0, $sub.i32(0, 2))'
// @checkbpl awk '/(__ubsan|llvm[.]ubsantrap|[.]src: ref)/ { exit 1 }'
// clang-format on

// Without sanitizer metadata the arithmetic carries no sign evidence at all.
// Negative add/sub/mul operands are still rendered signed: under the unbounded
// integer encoding that is the only spelling that computes the C decrement.

unsigned unsigned_add(unsigned x) { return x + 4294967293U; }

int signed_add(int x) { return x + -2; }

unsigned unsigned_sub(unsigned x) { return x - 4294967293U; }

int signed_sub(int x) { return x - -2; }

unsigned unsigned_mul(unsigned x) { return x * 4294967293U; }

int signed_mul(int x) { return x * -2; }

int main(void) {
  (void)unsigned_add(0);
  (void)signed_add(0);
  (void)unsigned_sub(0);
  (void)signed_sub(0);
  (void)unsigned_mul(0);
  (void)signed_mul(0);
  return 0;
}
