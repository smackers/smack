// @expect verified
// @flag -x svcomp --svcomp-property test/c/functionalize-loops/unreach-call.prp
// @checkbpl grep -q "functional read-only assertion loop summary for check"
// @checkout awk '/SMACK warning: found loop/ {x=1} END{exit x}'

extern void reach_error(void);

void __VERIFIER_assert(_Bool condition) {
  if (!condition)
    reach_error();
}

static void check(const unsigned char *a, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    __VERIFIER_assert(a[i] == 0);
}

int main(void) {
  unsigned char a[4096] = {0};
  check(a, 4096);
  return 0;
}
