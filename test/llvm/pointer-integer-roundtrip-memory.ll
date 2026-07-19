; @expect error
; @flag --integer-encoding=wrapped-integer

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i64 @to_integer(i32* %pointer) noinline {
  %integer = ptrtoint i32* %pointer to i64
  ret i64 %integer
}

define i32* @to_pointer(i64 %integer) noinline {
  %pointer = inttoptr i64 %integer to i32*
  ret i32* %pointer
}

define i32 @main() {
  %bytes = call i8* @malloc(i64 4)
  %pointer = bitcast i8* %bytes to i32*
  %integer = call i64 @to_integer(i32* %pointer)
  %roundtrip = call i32* @to_pointer(i64 %integer)

  store i32 0, i32* %roundtrip
  store i32 1, i32* %pointer
  %value = load i32, i32* %roundtrip
  %stale_value = icmp eq i32 %value, 0
  %assert_arg = zext i1 %stale_value to i32
  call void @__VERIFIER_assert(i32 %assert_arg)
  ret i32 0
}

declare i8* @malloc(i64)
declare void @__VERIFIER_assert(i32)
