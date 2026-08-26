; @expect error
;
; The failing twin of invoke_call_result.ll: the assertion claims @get returns
; something OTHER than what @set stored, which is false, so the slice must
; still report the error.

source_filename = "llvm-link"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@g = internal global i32 7

declare void @__VERIFIER_assert(i32)
declare i32 @__VERIFIER_nondet_int()
declare i32 @__gxx_personality_v0(...)

define internal void @set(i32 %x) {
  store i32 %x, i32* @g
  ret void
}

define internal i32 @get() {
  %v = load i32, i32* @g
  ret i32 %v
}

define i32 @main() personality i32 (...)* @__gxx_personality_v0 {
entry:
  %n0 = call i32 @__VERIFIER_nondet_int()
  %is7 = icmp eq i32 %n0, 7
  %n = select i1 %is7, i32 8, i32 %n0
  call void @set(i32 %n)
  %r = invoke i32 @get()
          to label %cont unwind label %lpad

cont:
  %ne = icmp ne i32 %r, %n
  %z = zext i1 %ne to i32
  call void @__VERIFIER_assert(i32 %z)
  ret i32 0

lpad:
  %ex = landingpad { i8*, i32 } cleanup
  resume { i8*, i32 } %ex
}
