//
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACK_H_
#define SMACK_H_

/**
 * The SMACK "prelude" declarations
 *
 * TODO add more documentation
 *
 * NOTES ON MEMORY MODELS
 *
 * 1. addresses are (unbounded) integers
 * 2. one unbounded integer is stored at each address
 * 3. (NO-REUSE only) heap addresses are allocated in a strictly increasing
 *    fashion
 * 4. (NO-REUSE only) freed (heap) addresses are never reallocated
 * 5. the address space is partitioned as follows
 *
 * Address A                                        Allocation
 * ---------                                        ----------
 * A > 0                                            Heap
 * A = 0                                            Not allocated (null)
 * $GLOBALS_BOTTOM <= A < 0                         Static (global storage)
 * $GLOBALS_BOTTOM - 32768 < A < $GLOBALS_BOTTOM    Not allocated (padding)
 * A < $GLOBALS_BOTTOM - 32768                      External
 *
 */

void __SMACK_code(const char *fmt, ...);
void __SMACK_mod(const char *fmt, ...);
void __SMACK_decl(const char *fmt, ...);
void __SMACK_top_decl(const char *fmt, ...);

void assert(int v) {
  __SMACK_code("assert @ != 0;", v);
}

void assume(int v) {
  __SMACK_code("assume @ != 0;", v);
}

//// PROBLEM: in the 2D memory model, the declaration of boogie_si_record_int
//// should have a type $ptr parameter, not an int.  How should we do this?
// void __SMACK_record_int(int i) {
//   __SMACK_top_decl("procedure boogie_si_record_int(i:int);");
//   __SMACK_code("call boogie_si_record_int(@);", i);
// }

int __SMACK_nondet() {
  static int XXX;
  int x = XXX;
  __SMACK_code("havoc @;", x);
  return x;
}

void __SMACK_decls() {
#define D(d) __SMACK_top_decl(d)

  // Integer arithmetic
  D("function {:inline} $add(p1:int, p2:int) returns (int) {p1 + p2}");
  D("function {:inline} $sub(p1:int, p2:int) returns (int) {p1 - p2}");
  D("function {:inline} $mul(p1:int, p2:int) returns (int) {p1 * p2}");
  D("function {:builtin \"div\"} $sdiv(p1:int, p2:int) returns (int);");
  D("function {:builtin \"div\"} $udiv(p1:int, p2:int) returns (int);");
  D("function {:builtin \"rem\"} $srem(p1:int, p2:int) returns (int);");
  D("function {:builtin \"rem\"} $urem(p1:int, p2:int) returns (int);");
  D("function $and(p1:int, p2:int) returns (int);");
  D("axiom $and(0,0) == 0;");
  D("axiom $and(0,1) == 0;");
  D("axiom $and(1,0) == 0;");
  D("axiom $and(1,1) == 1;");
  D("function $or(p1:int, p2:int) returns (int);");
  D("axiom $or(0,0) == 0;");
  D("axiom $or(0,1) == 1;");
  D("axiom $or(1,0) == 1;");
  D("axiom $or(1,1) == 1;");
  D("function $xor(p1:int, p2:int) returns (int);");
  D("axiom $xor(0,0) == 0;");
  D("axiom $xor(0,1) == 1;");
  D("axiom $xor(1,0) == 1;");
  D("axiom $xor(1,1) == 0;");
  D("function $lshr(p1:int, p2:int) returns (int);");
  D("function $ashr(p1:int, p2:int) returns (int);");
  D("function $shl(p1:int, p2:int) returns (int);");
  D("function {:inline} $ult(p1:int, p2:int) returns (bool) {p1 < p2}");
  D("function {:inline} $ugt(p1:int, p2:int) returns (bool) {p1 > p2}");
  D("function {:inline} $ule(p1:int, p2:int) returns (bool) {p1 <= p2}");
  D("function {:inline} $uge(p1:int, p2:int) returns (bool) {p1 >= p2}");
  D("function {:inline} $slt(p1:int, p2:int) returns (bool) {p1 < p2}");
  D("function {:inline} $sgt(p1:int, p2:int) returns (bool) {p1 > p2}");
  D("function {:inline} $sle(p1:int, p2:int) returns (bool) {p1 <= p2}");
  D("function {:inline} $sge(p1:int, p2:int) returns (bool) {p1 >= p2}");
  D("function $nand(p1:int, p2:int) returns (int);");
  D("function {:inline} $max(p1:int, p2:int) returns (int) {if p1 > p2 then p1 else p2}");
  D("function {:inline} $min(p1:int, p2:int) returns (int) {if p1 > p2 then p2 else p1}");
  D("function {:inline} $umax(p1:int, p2:int) returns (int) {if p1 > p2 then p1 else p2}");
  D("function {:inline} $umin(p1:int, p2:int) returns (int) {if p1 > p2 then p2 else p1}");
  D("function {:inline} $i2b(i: int) returns (bool) {i != 0}");
  D("function {:inline} $b2i(b: bool) returns (int) {if b then 1 else 0}");

  // Floating point
  D("type float;");
  D("function $fp(ipart:int, fpart:int, epart:int) returns (float);");
  D("function $fadd(f1:float, f2:float) returns (float);");
  D("function $fsub(f1:float, f2:float) returns (float);");
  D("function $fmul(f1:float, f2:float) returns (float);");
  D("function $fdiv(f1:float, f2:float) returns (float);");
  D("function $frem(f1:float, f2:float) returns (float);");
  D("function $ffalse(f1:float, f2:float) returns (bool);");
  D("function $ftrue(f1:float, f2:float) returns (bool);");
  D("function $foeq(f1:float, f2:float) returns (bool);");
  D("function $foge(f1:float, f2:float) returns (bool);");
  D("function $fogt(f1:float, f2:float) returns (bool);");
  D("function $fole(f1:float, f2:float) returns (bool);");
  D("function $folt(f1:float, f2:float) returns (bool);");
  D("function $fone(f1:float, f2:float) returns (bool);");
  D("function $ford(f1:float, f2:float) returns (bool);");
  D("function $fueq(f1:float, f2:float) returns (bool);");
  D("function $fuge(f1:float, f2:float) returns (bool);");
  D("function $fugt(f1:float, f2:float) returns (bool);");
  D("function $fule(f1:float, f2:float) returns (bool);");
  D("function $fult(f1:float, f2:float) returns (bool);");
  D("function $fune(f1:float, f2:float) returns (bool);");
  D("function $funo(f1:float, f2:float) returns (bool);");
  D("function $fp2si(f:float) returns (int);");
  D("function $fp2ui(f:float) returns (int);");
  D("function $si2fp(i:int) returns (float);");
  D("function $ui2fp(i:int) returns (float);");

  D("axiom (forall f1, f2: float :: f1 != f2 || $foeq(f1,f2));");
  D("axiom (forall i: int :: $fp2ui($ui2fp(i)) == i);");
  D("axiom (forall f: float :: $ui2fp($fp2ui(f)) == f);");
  D("axiom (forall i: int :: $fp2si($si2fp(i)) == i);");
  D("axiom (forall f: float :: $si2fp($fp2si(f)) == f);");

  // Memory Model
  D("function $base(int) returns (int);");

  D("const unique $NULL: int;");
  D("axiom $NULL == 0;");
  D("const $UNDEF: int;");

  D("function {:inline} $pa(pointer: int, index: int, size: int) returns (int) {pointer + index * size}");
  D("function {:inline} $trunc(p: int, size: int) returns (int) {p}");
  D("function {:inline} $p2i(p: int) returns (int) {p}");
  D("function {:inline} $i2p(p: int) returns (int) {p}");
  D("function {:inline} $p2b(p: int) returns (bool) {p != 0}");
  D("function {:inline} $b2p(b: bool) returns (int) {if b then 1 else 0}");

  // Memory debugging symbols
  D("type $mop;");
  D("procedure boogie_si_record_mop(m: $mop);");
  D("procedure boogie_si_record_bool(b: bool);");
  D("procedure boogie_si_record_int(i: int);");
  D("procedure boogie_si_record_float(f: float);");
  D("const $MOP: $mop;");
  
  D("const $GLOBALS_BOTTOM: int;");
  D("function {:inline} $isExternal(p: int) returns (bool) { p < $GLOBALS_BOTTOM - 32768 }");
  
#if MEMORY_MODEL_NO_REUSE_IMPLS
  D("var $Alloc: [int] bool;");
  D("var $CurrAddr:int;");

  D("procedure $malloc(n: int) returns (p: int)\n"
    "modifies $CurrAddr, $Alloc;\n"
    "{\n"
    "  assume $CurrAddr > 0;\n"
    "  p := $CurrAddr;\n"
    "  if (n > 0) {\n"
    "    $CurrAddr := $CurrAddr + n;\n"
    "  } else {\n"
    "    $CurrAddr := $CurrAddr + 1;\n"
    "  }\n"
    "  $Alloc[p] := true;\n"
    "}");

  D("procedure $free(p: int)\n"
    "modifies $Alloc;\n"
    "{\n"
    "  $Alloc[p] := false;\n"
    "}");
  
  D("procedure $alloca(n: int) returns (p: int)\n"
    "modifies $CurrAddr, $Alloc;\n"
    "{\n"
    "  assume $CurrAddr > 0;\n"
    "  p := $CurrAddr;\n"
    "  if (n > 0) {\n"
    "    $CurrAddr := $CurrAddr + n;\n"
    "  } else {\n"
    "    $CurrAddr := $CurrAddr + 1;\n"
    "  }\n"
    "  $Alloc[p] := true;\n"
    "}");

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
  D("var $Alloc: [int] bool;");
  D("var $Size: [int] int;");

  D("procedure $malloc(n: int) returns (p: int);\n"
    "modifies $Alloc, $Size;\n"
    "ensures p > 0;\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: int :: old($Alloc[q]) ==> (p + n < q || p > q + $Size[q]));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: int :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures n >= 0 ==> (forall q: int :: {$base(q)} p <= q && q < p+n ==> $base(q) == p);");

  D("procedure $free(p: int);\n"
    "modifies $Alloc;\n"
    "ensures !$Alloc[p];\n"
    "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));");

  D("procedure $alloca(n: int) returns (p: int);\n"
    "modifies $Alloc, $Size;\n"
    "ensures p > 0;\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: int :: old($Alloc[q]) ==> (p + n < q || p > q + $Size[q]));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: int :: {$Size[q]} q != p ==> $Size[q] == old($Size[q]));\n"
    "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures n >= 0 ==> (forall q: int :: {$base(q)} p <= q && q < p+n ==> $base(q) == p);");

#else // NO_REUSE does not reuse previously-allocated addresses
  D("var $Alloc: [int] bool;");
  D("var $CurrAddr:int;");

  D("procedure $malloc(n: int) returns (p: int);\n"
    "modifies $CurrAddr, $Alloc;\n"
    "ensures p > 0;\n"
    "ensures p == old($CurrAddr);\n"
    "ensures $CurrAddr > old($CurrAddr);\n"
    "ensures n >= 0 ==> $CurrAddr >= old($CurrAddr) + n;\n"
    "ensures $Alloc[p];\n"
    "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures n >= 0 ==> (forall q: int :: {$base(q)} p <= q && q < p+n ==> $base(q) == p);");

  D("procedure $free(p: int);\n"
    "modifies $Alloc;\n"
    "ensures !$Alloc[p];\n"
    "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));");

  D("procedure $alloca(n: int) returns (p: int);\n"
    "modifies $CurrAddr, $Alloc;\n"
    "ensures p > 0;\n"
    "ensures p == old($CurrAddr);\n"
    "ensures $CurrAddr > old($CurrAddr);\n"
    "ensures n >= 0 ==> $CurrAddr >= old($CurrAddr) + n;\n"
    "ensures $Alloc[p];\n"
    "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures n >= 0 ==> (forall q: int :: {$base(q)} p <= q && q < p+n ==> $base(q) == p);");
#endif

  D("var $exn: bool;");
  D("var $exnv: int;");
  D("function $extractvalue(p: int, i: int) returns (int);");

#undef D
}

#endif /*SMACK_H_*/
