// This file is distributed under the MIT License. See LICENSE for details.
// Without --sign-analysis the translation must stay byte-identical to the
// legacy output. The spellings pinned below are the legacy per-opcode
// heuristic, not the correct rendering: `x - -2` on an int is printed as
// `$sub.i32($i0, 4294967294)`, which does not compute x + 2 under the
// unbounded integer encoding. See docs/sign-analysis.md.
// @expect verified
// clang-format off
// @checkbpl grep -F '$add.i32($i0, 4294967294)'
// @checkbpl grep -F '$add.i32($i0, $sub.i32(0, 2))'
// @checkbpl awk 'index($0, "$sub.i32($i0, 4294967294)") { n++ } END { exit n != 2 }'
// @checkbpl awk '/(__ubsan|llvm[.]ubsantrap|[.]src: ref)/ { exit 1 }'
// clang-format on

unsigned unsigned_add(unsigned x) { return x + 4294967294U; }

int signed_add(int x) { return x + -2; }

unsigned unsigned_sub(unsigned x) { return x - 4294967294U; }

int signed_sub(int x) { return x - -2; }

int main(void) {
  (void)unsigned_add(0);
  (void)signed_add(0);
  (void)unsigned_sub(0);
  (void)signed_sub(0);
  return 0;
}
