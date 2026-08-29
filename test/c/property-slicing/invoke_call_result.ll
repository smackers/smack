; @expect verified
;
; An `invoke` whose RESULT the assertion consumes. Hand-written LLVM IR
; because SMACK's C front end never emits an invoke: default_clang_compile_command
; (share/smack/frontend.py:88-121) passes no -fexceptions, so clang marks every
; C function nounwind and lowers every call as a `call`. C++ is the natural
; source of invokes, and test/cplusplus is skipped in this tree.
;
; The property-slicing rule under test is "a relevant call result makes the
; callee's returned values relevant". Written over CallInst alone it does not
; fire here, and then nothing marks @get's load as relevant, the region behind
; @g is never relevant, and the store inside @set -- together with the whole
; `call @set` and the static initialiser of @g -- is sliced away. $M.0 is then
; unconstrained and this verified program reports a spurious error.

source_filename = "llvm-link"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; A non-zero initialiser: SMACK emits __SMACK_static_init only for those, and
; the test needs @g's starting value to be pinned rather than unconstrained.
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
  ; n is nondeterministic but never 7, so reading @g's initial value instead
  ; of what @set wrote is observable.
  %n = select i1 %is7, i32 8, i32 %n0
  call void @set(i32 %n)
  %r = invoke i32 @get()
          to label %cont unwind label %lpad

cont:
  %eq = icmp eq i32 %r, %n
  %z = zext i1 %eq to i32
  call void @__VERIFIER_assert(i32 %z)
  ret i32 0

lpad:
  %ex = landingpad { i8*, i32 } cleanup
  resume { i8*, i32 } %ex
}
