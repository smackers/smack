; @expect verified
; @flag --unroll=4

; The insertvalue runs once per iteration with a different value. Its result
; must take the value of the last iteration, 1.

target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare void @__VERIFIER_assert(i32)

define i32 @get({ i32, i32 } %s) noinline {
  %f = extractvalue { i32, i32 } %s, 0
  ret i32 %f
}

define i32 @main() {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %next, %loop ]
  %acc = phi { i32, i32 } [ undef, %entry ], [ %s, %loop ]
  %s = insertvalue { i32, i32 } %acc, i32 %i, 0
  %next = add i32 %i, 1
  %c = icmp slt i32 %next, 2
  br i1 %c, label %loop, label %exit
exit:
  %f = call i32 @get({ i32, i32 } %s)
  %ok = icmp eq i32 %f, 1
  %oka = zext i1 %ok to i32
  call void @__VERIFIER_assert(i32 %oka)
  ret i32 0
}
