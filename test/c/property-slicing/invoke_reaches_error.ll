; @expect verified
;
; The property root reached THROUGH an invoke: @main invokes @check, and it is
; @check that calls __VERIFIER_assert. This is the shape that computeMayReachError
; and the per-argument rule of `propagate` have to see -- both of which used to
; be written over CallInst and so recorded no call-graph edge and no argument
; binding at an invoke at all.

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
  %n0 = call i32 @__VERIFIER_nondet_int()
  %is0 = icmp eq i32 %n0, 0
  ; nondeterministic, but never 0 -- so the assertion holds without being
  ; vacuous.
  %n = select i1 %is0, i32 1, i32 %n0
  invoke void @check(i32 %n)
          to label %cont unwind label %lpad

cont:
  ret i32 0

lpad:
  %ex = landingpad { i8*, i32 } cleanup
  resume { i8*, i32 } %ex
}
