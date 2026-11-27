; @expect error

; Names that are Boogie 3 keywords, in the places clang does not name in C
; but other frontends and hand-written IR do: a parameter and block labels.
; Boogie rejects push, pop, hide and reveal only as labels (issue #842).

target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare void @__VERIFIER_assert(i32)
declare i32 @__VERIFIER_nondet_int()

@uses = global i32 7

define i32 @measure(i32 %is) noinline {
push:
  %a = add i32 %is, 1
  br label %pop
pop:
  %b = sub i32 %a, 1
  br label %hide
hide:
  br label %reveal
reveal:
  ret i32 %b
}

define i32 @main() {
entry:
  %n = call i32 @__VERIFIER_nondet_int()
  %u = load i32, i32* @uses
  %r = call i32 @measure(i32 %n)
  %c = icmp ne i32 %r, %n
  %ci = zext i1 %c to i32
  call void @__VERIFIER_assert(i32 %ci)
  %d = icmp eq i32 %u, 7
  %di = zext i1 %d to i32
  call void @__VERIFIER_assert(i32 %di)
  ret i32 0
}
