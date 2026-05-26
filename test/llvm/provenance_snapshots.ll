; @expect verified
; @flag --entry-points=main
; @checkbpl grep '{:snapshot_kind "loop_entry"}'
; @checkbpl grep '{:snapshot_var "'
; @checkbpl grep '.pre"}'

source_filename = "provenance_snapshots.ll"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @main() {
entry:
  br label %loop

loop:
  %i = phi i32 [ 0, %entry ], [ %next, %body ]
  %cmp = icmp slt i32 %i, 2
  br i1 %cmp, label %body, label %exit

body:
  %next = add i32 %i, 1
  br label %loop

exit:
  ret i32 %i
}
