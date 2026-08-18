// This file is distributed under the MIT License. See LICENSE for details.
// @expect verified
// clang-format off
// @checkbpl grep -F '$add.i32($i0, 4294967280)'
// @checkbpl grep -F '$add.i32($i0, $sub.i32(0, 16))'
// @checkbpl awk '/procedure (unsigned_add|signed_add)/,/^}/ { if (/call (__ubsan_handle|__SMACK_check_overflow)/) exit 1 }'
// clang-format on

unsigned unsigned_add(unsigned x) { return x + 4294967280U; }

int signed_add(int x) { return x + -16; }

int main(void) {
  (void)unsigned_add(0);
  (void)signed_add(0);
  return 0;
}
