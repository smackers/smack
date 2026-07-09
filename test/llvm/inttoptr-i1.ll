; @expect verified
; @checkbpl grep "function .*\$i2p\.i1\.ref"
; @checkbpl grep ":= \$i2p\.i1\.ref"

source_filename = "inttoptr-i1"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @main() {
entry:
  %b = call i1 @__VERIFIER_nondet_bool()
  %p = inttoptr i1 %b to ptr
  call void @opaque_sink(ptr %p)
  call void @__VERIFIER_assert(i32 1)
  ret i32 0
}

declare i1 @__VERIFIER_nondet_bool()
declare void @opaque_sink(ptr)
declare void @__VERIFIER_assert(i32)
