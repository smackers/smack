// This file is distributed under the MIT License. See LICENSE for details.
// @expect verified
// clang-format off
// @checkbpl grep -F '$add.i32($i0, 4294967280)'
// @checkbpl grep -F '$add.i32($i0, $sub.i32(0, 16))'
// @checkbpl grep -F '$sub.i32($i0, 4294967280)'
// @checkbpl grep -F '$sub.i32($i0, $sub.i32(0, 16))'
// @checkbpl grep -F 'then 4294967280 else 0'
// @checkbpl grep -F 'then $sub.i32(0, 16) else 0'
// @checkbpl awk '/procedure  (unsigned|signed)_(add|sub|select)/,/^}/ { if (/call (__ubsan_handle|__SMACK_check_overflow)/) exit 1 }'
// clang-format on

unsigned unsigned_add(unsigned x) { return x + 4294967280U; }

int signed_add(int x) { return x + -16; }

unsigned unsigned_sub(unsigned x) { return x - 4294967280U; }

int signed_sub(int x) { return x - -16; }

unsigned unsigned_select(int c, unsigned x) {
  return x + (c ? 4294967280U : 0U);
}

int signed_select(int c, int x) { return x + (c ? -16 : 0); }

int main(void) {
  (void)unsigned_add(0);
  (void)signed_add(0);
  (void)unsigned_sub(0);
  (void)signed_sub(0);
  (void)unsigned_select(0, 0);
  (void)signed_select(0, 0);
  return 0;
}
