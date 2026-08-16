; @expect verified
; @flag --entry-points=foo
; @checkout grep -F "SMACK warning: found loop in function foo"
; @checkout grep -F "in function foo: --unroll=10 is needed"

; A loop in a module with no debug info at all. `Loop::getLocRange()` hands
; back a pair of null DebugLocs for it, and calling getLine() on one of those
; is a plain null dereference rather than a failed assertion, because the LLVM
; that most distributions ship is built with assertions off. The loop-bound
; warning has to degrade to naming just the function instead of crashing.
;
; Bitcode reaches SMACK this way routinely: the .bc/.ll frontend passes user
; input through untouched, so nothing ever adds debug info to it.

source_filename = "loop_no_debug_info"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define internal i32 @foo() {
entry:
  br label %head

head:
  %i = phi i32 [ 0, %entry ], [ %next, %head ]
  %next = add nsw i32 %i, 1
  %cmp = icmp slt i32 %next, 10
  br i1 %cmp, label %head, label %exit

exit:
  ret i32 %i
}
