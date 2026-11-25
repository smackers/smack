; @expect error
;
; The failing twin of invoke_reaches_error.ll: the nondeterministic value is
; passed to @check unguarded, so the assertion inside the invoked callee is
; reachable and the slice must keep the whole chain.

source_filename = "llvm-link"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare void @__VERIFIER_assert(i32)
declare i32 @__VERIFIER_nondet_int()
declare i32 @__gxx_personality_v0(...)

define internal void @check(i32 %x) {
  %nz = icmp ne i32 %x, 0
  %z = zext i1 %nz to i32
  call void @__VERIFIER_assert(i32 %z)
  ret void
}

define i32 @main() personality i32 (...)* @__gxx_personality_v0 {
entry:
  %n = call i32 @__VERIFIER_nondet_int()
  invoke void @check(i32 %n)
          to label %cont unwind label %lpad

cont:
  ret i32 0

lpad:
  %ex = landingpad { i8*, i32 } cleanup
  resume { i8*, i32 } %ex
}
