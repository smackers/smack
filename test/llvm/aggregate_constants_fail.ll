; @expect error

; Struct and array constants used as values: in a phi, in a select and as a
; call argument, including a zeroinitializer and a nested constant array.

target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare void @__VERIFIER_assert(i32)

%pair = type { i32, [2 x i8] }

define i32 @sum(%pair %p) noinline {
  %a = extractvalue %pair %p, 0
  %b = extractvalue %pair %p, 1, 1
  %bz = zext i8 %b to i32
  %r = add i32 %a, %bz
  ret i32 %r
}

declare i32 @__VERIFIER_nondet_int()

define i32 @main() {
entry:
  %n = call i32 @__VERIFIER_nondet_int()
  %c = icmp sgt i32 %n, 0
  br i1 %c, label %then, label %join
then:
  br label %join
join:
  %p = phi %pair [ { i32 1, [2 x i8] c"ab" }, %then ], [ zeroinitializer, %entry ]
  %q = select i1 %c, %pair %p, %pair { i32 5, [2 x i8] zeroinitializer }
  ; then: 1 + 'b' (98); otherwise 5 + 0, not 6
  %r = call i32 @sum(%pair %q)
  %expected = select i1 %c, i32 99, i32 6
  %ok = icmp eq i32 %r, %expected
  %oka = zext i1 %ok to i32
  call void @__VERIFIER_assert(i32 %oka)
  %z = call i32 @sum(%pair zeroinitializer)
  %okz = icmp eq i32 %z, 0
  %okza = zext i1 %okz to i32
  call void @__VERIFIER_assert(i32 %okza)
  ret i32 0
}
