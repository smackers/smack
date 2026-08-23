; @expect verified
; @checkbpl grep -F '$sub.i32(x, $sub.i32(0, 16))'
; @checkbpl grep -F '$sub.i32(x, 4294967280)'
; @checkbpl grep -F 'then $sub.i32(0, 16) else 0'
; @checkbpl grep -F 'then 4294967280 else 0'
; @checkbpl grep -F '$eq.i32($i0, $sub.i32(0, 16))'
; @checkbpl grep -F '$eq.i32($i0, $sub.i32(0, 17))'
; @checkbpl grep -F '$ne.i32($i0, $sub.i32(0, 18))'
; @checkbpl grep -F '$si2fp.i32.float($sub.i32(0, 16))'
; @checkbpl grep -F '$ui2fp.i32.float(4294967280)'
; @checkbpl grep -F 'signed_arg($sub.i32(0, 16))'
; @checkbpl grep -F 'unsigned_arg(4294967280)'
; @checkbpl grep -F '$add.i32(x, 4294967294)'
; @checkbpl grep -F '$add.i32(x, $sub.i32(0, 2))'
; @checkbpl grep -F '$sub.i32(x, 4294967294)'
; @checkbpl grep -F '$sub.i32(x, $sub.i32(0, 2))'
; @checkbpl grep -F '$mul.i32(x, 4294967294)'
; @checkbpl grep -F '$mul.i32(x, $sub.i32(0, 2))'
; @checkbpl grep -F 'phi_unsigned_arg(1, 9223372036854775808)'
; @checkbpl grep -F 'phi_signed_arg(1, $sub.i64(0, 2))'
; @checkbpl grep -F 'ashr_operands($sub.i32(0, 2), 4294967294)'
; @checkbpl grep -F 'shl_count($sub.i32(0, 2), 4294967294)'
; @checkbpl grep -F '$i1 := $add.i32($i0, $sub.i32(0, 3))'
; @checkbpl grep -F '$i2 := $add.i32($i1, $sub.i32(0, 2))'

define i32 @signed_sub(i32 %x) {
  %r = sub i32 %x, -16, !overflow.sign !0
  ret i32 %r
}

define i32 @unsigned_sub(i32 %x) {
  %r = sub i32 %x, -16, !overflow.sign !1
  ret i32 %r
}

define i32 @signed_select(i1 %c, i32 %x) {
  %choice = select i1 %c, i32 -16, i32 0
  %r = add i32 %x, %choice, !overflow.sign !0
  ret i32 %r
}

define i32 @unsigned_select(i1 %c, i32 %x) {
  %choice = select i1 %c, i32 -16, i32 0
  %r = add i32 %x, %choice, !overflow.sign !1
  ret i32 %r
}

define i1 @signed_eq(i32 %x) {
  %seed = add i32 %x, 0, !overflow.sign !0
  %r = icmp eq i32 %seed, -16
  ret i1 %r
}

define i1 @unsigned_eq(i32 %x) {
  %seed = add i32 %x, 0, !overflow.sign !1
  %r = icmp eq i32 %seed, -17
  ret i1 %r
}

define internal i32 @unsigned_result(i32 %x) {
  %r = add i32 %x, 0, !overflow.sign !1
  ret i32 %r
}

define i1 @unsigned_ne(i32 %x) {
  %seed = call i32 @unsigned_result(i32 %x)
  %r = icmp ne i32 %seed, -18
  ret i1 %r
}

define float @signed_fp() {
  %r = sitofp i32 -16 to float
  ret float %r
}

define float @unsigned_fp() {
  %r = uitofp i32 -16 to float
  ret float %r
}

define internal i32 @signed_arg(i32 %x) {
  %r = add i32 %x, 1, !overflow.sign !0
  ret i32 %r
}

define internal i32 @unsigned_arg(i32 %x) {
  %r = add i32 %x, 1, !overflow.sign !1
  ret i32 %r
}

; These model uninstrumented library IR. Unknown arithmetic must retain the
; legacy local fallback, while nsw remains definite signed evidence.
define internal i32 @plain_unsigned_add(i32 %x) {
  %r = add i32 %x, -2
  ret i32 %r
}

define internal i32 @plain_signed_add(i32 %x) {
  %r = add nsw i32 %x, -2
  ret i32 %r
}

define internal i32 @plain_unsigned_sub(i32 %x) {
  %r = sub i32 %x, -2
  ret i32 %r
}

define internal i32 @plain_signed_sub(i32 %x) {
  %r = sub nsw i32 %x, -2
  ret i32 %r
}

define internal i32 @plain_unsigned_mul(i32 %x) {
  %r = mul i32 %x, -2
  ret i32 %r
}

define internal i32 @plain_signed_mul(i32 %x) {
  %r = mul nsw i32 %x, -2
  ret i32 %r
}

; The sign evidence for the call argument is beyond a PHI. This is the shape
; used by true large size_t constants in the AWS benchmarks.
define internal i1 @phi_unsigned_arg(i1 %c, i64 %x) {
entry:
  br i1 %c, label %left, label %right
left:
  br label %merge
right:
  br label %merge
merge:
  %p = phi i64 [ %x, %left ], [ 0, %right ]
  %r = icmp ule i64 %p, 42
  ret i1 %r
}

define internal i1 @phi_signed_arg(i1 %c, i64 %x) {
entry:
  br i1 %c, label %left, label %right
left:
  br label %merge
right:
  br label %merge
merge:
  %p = phi i64 [ %x, %left ], [ 0, %right ]
  %r = icmp sle i64 %p, 42
  ret i1 %r
}

; Shift values and counts have different interpretations.
define internal i32 @ashr_operands(i32 %x, i32 %amount) {
  %r = ashr i32 %x, %amount
  ret i32 %r
}

define internal i32 @shl_count(i32 %x, i32 %amount) {
  %r = shl i32 %x, %amount
  ret i32 %r
}

; Both additions belong to the same cyclic use graph, but only %b has direct
; signed evidence. Resolving %b first must not cache a provisional Unknown for
; %a and make the second literal use fall back to unsigned.
define internal i32 @cycle_cache(i32 %x) {
entry:
  br label %loop
loop:
  %p = phi i32 [ %x, %entry ], [ %a, %loop ]
  %b = add i32 %p, -3
  %a = add i32 %b, -2
  %cmp = icmp slt i32 %b, 0
  br i1 %cmp, label %loop, label %exit
exit:
  ret i32 %a
}

define i32 @main() {
  %s0 = call i32 @signed_sub(i32 0)
  %u0 = call i32 @unsigned_sub(i32 0)
  %s1 = call i32 @signed_select(i1 true, i32 0)
  %u1 = call i32 @unsigned_select(i1 true, i32 0)
  %s2 = call i1 @signed_eq(i32 0)
  %u2 = call i1 @unsigned_eq(i32 0)
  %u2ne = call i1 @unsigned_ne(i32 0)
  %s3 = call float @signed_fp()
  %u3 = call float @unsigned_fp()
  %s4 = call i32 @signed_arg(i32 -16)
  %u4 = call i32 @unsigned_arg(i32 -16)
  %lu0 = call i32 @plain_unsigned_add(i32 0)
  %ls0 = call i32 @plain_signed_add(i32 0)
  %lu1 = call i32 @plain_unsigned_sub(i32 0)
  %ls1 = call i32 @plain_signed_sub(i32 0)
  %lu2 = call i32 @plain_unsigned_mul(i32 0)
  %ls2 = call i32 @plain_signed_mul(i32 0)
  %pu = call i1 @phi_unsigned_arg(i1 true, i64 -9223372036854775808)
  %ps = call i1 @phi_signed_arg(i1 true, i64 -2)
  %as = call i32 @ashr_operands(i32 -2, i32 -2)
  %sh = call i32 @shl_count(i32 -2, i32 -2)
  %cy = call i32 @cycle_cache(i32 4)
  ret i32 0
}

!0 = !{!"s"}
!1 = !{!"u"}
