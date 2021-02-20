#include <stdint.h>
#include <stdlib.h>

#define mk_signed_type(size) int##size##_t
#define mk_unsigned_type(size) uint##size##_t

#define mk_signed_min(size) INT##size##_MIN
#define mk_signed_max(size) INT##size##_MAX
#define mk_unsigned_min(size) 0
#define mk_unsigned_max(size) UINT##size##_MAX

#define mk_smack_signed_nondet(size) __SMACK_nondet_i##size
#define mk_smack_unsigned_nondet(size) __SMACK_nondet_u##size
#define mk_smack_nondet_decl(size)                                             \
  mk_signed_type(size) mk_smack_signed_nondet(size)(void);                     \
  mk_unsigned_type(size) mk_smack_unsigned_nondet(size)(void);

#define mk_smack_nondet_def(size)                                              \
  mk_signed_type(size) __VERIFIER_nondet_i##size(void) {                       \
    mk_signed_type(size) ret = mk_smack_signed_nondet(size)();                 \
    if (ret < mk_signed_min(size) || ret > mk_signed_max(size))                \
      abort();                                                                 \
    return ret;                                                                \
  }                                                                            \
  mk_unsigned_type(size) __VERIFIER_nondet_u##size(void) {                     \
    mk_unsigned_type(size) ret = mk_smack_unsigned_nondet(size)();             \
    if (ret < mk_unsigned_min(size) || ret > mk_unsigned_max(size))            \
      abort();                                                                 \
    return ret;                                                                \
  }

#define mk_dummy_int_nondet_def(size)                                          \
  mk_signed_type(size) __VERIFIER_nondet_i##size(void) {                       \
    return *((mk_signed_type(size) *)malloc(sizeof(mk_signed_type(size))));    \
  }                                                                            \
  mk_unsigned_type(size) __VERIFIER_nondet_u##size(void) {                     \
    return *(                                                                  \
        (mk_unsigned_type(size) *)malloc(sizeof(mk_unsigned_type(size))));     \
  }

#define mk_dummy_fp_nondet_def(ty)                                             \
  ty __VERIFIER_nondet_##ty(void) { return *((ty *)malloc(sizeof(ty))); }

#if CARGO_BUILD
mk_dummy_int_nondet_def(8) mk_dummy_int_nondet_def(16)
    mk_dummy_int_nondet_def(32) mk_dummy_int_nondet_def(64)
        mk_dummy_fp_nondet_def(float)
            mk_dummy_fp_nondet_def(double) void __VERIFIER_assert(int x) {}
void __VERIFIER_assume(int x) {}
#else
mk_smack_nondet_decl(8) mk_smack_nondet_decl(16) mk_smack_nondet_decl(32)
    mk_smack_nondet_decl(64) mk_smack_nondet_def(8) mk_smack_nondet_def(16)
        mk_smack_nondet_def(32) mk_smack_nondet_def(64)
#endif
