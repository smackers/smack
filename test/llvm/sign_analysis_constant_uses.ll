; @expect verified
; @checkbpl grep -F '$sub.i32(x, $sub.i32(0, 16))'
; @checkbpl grep -F '$sub.i32(x, 4294967280)'
; @checkbpl grep -F 'then $sub.i32(0, 16) else 0'
; @checkbpl grep -F 'then 4294967280 else 0'
; @checkbpl grep -F '$eq.i32($i0, $sub.i32(0, 16))'
; @checkbpl grep -F '$eq.i32($i0, 4294967280)'
; @checkbpl grep -F '$si2fp.i32.float($sub.i32(0, 16))'
; @checkbpl grep -F '$ui2fp.i32.float(4294967280)'
; @checkbpl grep -F 'signed_arg($sub.i32(0, 16))'
; @checkbpl grep -F 'unsigned_arg(4294967280)'

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
  %r = icmp eq i32 %seed, -16
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

define i32 @main() {
  %s0 = call i32 @signed_sub(i32 0)
  %u0 = call i32 @unsigned_sub(i32 0)
  %s1 = call i32 @signed_select(i1 true, i32 0)
  %u1 = call i32 @unsigned_select(i1 true, i32 0)
  %s2 = call i1 @signed_eq(i32 0)
  %u2 = call i1 @unsigned_eq(i32 0)
  %s3 = call float @signed_fp()
  %u3 = call float @unsigned_fp()
  %s4 = call i32 @signed_arg(i32 -16)
  %u4 = call i32 @unsigned_arg(i32 -16)
  ret i32 0
}

!0 = !{!"s"}
!1 = !{!"u"}
