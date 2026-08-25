// This file is distributed under the MIT License. See LICENSE for details.
// @expect verified
// @flag --sign-analysis
// clang-format off
// @checkbpl grep -F '$add.i32($i0, $sub.i32(0, 17))'
// @checkbpl grep -F '$add.i32($i0, $sub.i32(0, 16))'
// @checkbpl grep -F '$sub.i32($i0, $sub.i32(0, 17))'
// @checkbpl grep -F '$sub.i32($i0, $sub.i32(0, 16))'
// @checkbpl grep -F '$mul.i32($i0, $sub.i32(0, 17))'
// @checkbpl grep -F '$mul.i32($i0, $sub.i32(0, 16))'
// @checkbpl grep -F 'then 4294967280 else 0'
// @checkbpl grep -F 'then $sub.i32(0, 16) else 0'
// @checkbpl awk '/(__ubsan|llvm[.]ubsantrap|[.]src: ref)/ { exit 1 }'
// clang-format on

// Negative literals that are direct add/sub/mul operands are rendered signed
// even when the sanitizer tags the operation "u": under the unbounded integer
// encoding x + (2^32 - 17) never wraps, so x + (-17) is the only spelling that
// computes the C result. The tag still decides the window of a value that
// flows into the operation, e.g. the select arms below.

unsigned unsigned_add(unsigned x) { return x + 4294967279U; }

int signed_add(int x) { return x + -16; }

unsigned unsigned_sub(unsigned x) { return x - 4294967279U; }

int signed_sub(int x) { return x - -16; }

unsigned unsigned_mul(unsigned x) { return x * 4294967279U; }

int signed_mul(int x) { return x * -16; }

unsigned unsigned_select(int c, unsigned x) {
  return x + (c ? 4294967280U : 0U);
}

int signed_select(int c, int x) { return x + (c ? -16 : 0); }

int signed_div(int x, int y) { return x / y; }

int main(void) {
  (void)unsigned_add(0);
  (void)signed_add(0);
  (void)unsigned_sub(0);
  (void)signed_sub(0);
  (void)unsigned_mul(0);
  (void)signed_mul(0);
  (void)unsigned_select(0, 0);
  (void)signed_select(0, 0);
  (void)signed_div(4, 2);
  return 0;
}
