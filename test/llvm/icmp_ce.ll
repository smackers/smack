; @expect verified
; @checkbpl grep -F '$zext.i1.i32($slt.i64($p2i.ref.i64(g), $sub.i64(0, 1)))'

; An icmp constant expression whose operand is a negative literal. The user of
; the literal is a ConstantExpr, not an Instruction, so the literal sign lookup
; must not cast the (null) instruction pointer. Clang emits this shape for a
; pointer compared against a negative constant.
@g = global i32 0, align 4

define i32 @main() {
entry:
  %x = zext i1 icmp slt (i64 ptrtoint (i32* @g to i64), i64 -1) to i32
  ret i32 %x
}
