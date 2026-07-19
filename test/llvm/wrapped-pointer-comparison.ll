; @expect verified
; @flag --integer-encoding=wrapped-integer

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @main() {
  %base_value = call i64 @__SMACK_nondet_unsigned_long_long()
  %is_signed_max = icmp eq i64 %base_value, 9223372036854775807
  %base_assume_arg = zext i1 %is_signed_max to i32
  call void @__VERIFIER_assume(i32 %base_assume_arg)

  %base_pointer = inttoptr i64 %base_value to i8*
  %incremented_pointer = getelementptr i8, i8* %base_pointer, i64 1
  %signed_min_pointer = inttoptr i64 -9223372036854775808 to i8*
  %arithmetic_is_correct = icmp eq i8* %incremented_pointer, %signed_min_pointer

  %value = call i64 @__SMACK_nondet_unsigned_long_long()
  %is_minus_one = icmp eq i64 %value, -1
  %assume_arg = zext i1 %is_minus_one to i32
  call void @__VERIFIER_assume(i32 %assume_arg)

  %pointer = inttoptr i64 %value to i8*
  %is_unsigned_lt_null = icmp ult i8* %pointer, null
  %is_signed_lt_null = icmp slt i8* %pointer, null
  %is_not_unsigned_lt_null = xor i1 %is_unsigned_lt_null, true
  %comparison_is_correct = and i1 %is_not_unsigned_lt_null, %is_signed_lt_null
  %result_is_correct = and i1 %arithmetic_is_correct, %comparison_is_correct
  %assert_arg = zext i1 %result_is_correct to i32
  call void @__VERIFIER_assert(i32 %assert_arg)
  ret i32 0
}

declare i64 @__SMACK_nondet_unsigned_long_long()
declare void @__VERIFIER_assume(i32)
declare void @__VERIFIER_assert(i32)
