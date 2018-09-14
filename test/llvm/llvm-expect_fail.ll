; @expect error

; This file tests that the semantics of the llvm.expect intrinsic is properly
; modeled.
; ModuleID = '/home/vagrant/rust-smack/b-Y00Q2K.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind uwtable
define i32 @main() {
  %1 = add nsw i32 0, 1
  %2 = call i32 @llvm.expect.i32(i32 0, i32 1)
  call void @__VERIFIER_assert(i32 %2)
  ret i32 0
}

declare i32 @llvm.expect.i32(i32, i32)
declare void @__VERIFIER_assert(i32)