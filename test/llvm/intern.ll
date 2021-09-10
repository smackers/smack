; @expect verified
; @flag --entry-points=foo

source_filename = "llvm-link"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind uwtable
define internal i32 @foo() {
  call void @__VERIFIER_assert(i32 1)
  ret i32 0
}

declare void @__VERIFIER_assert(i32)