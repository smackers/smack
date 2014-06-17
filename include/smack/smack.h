//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
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

#include <stdbool.h>

void __SMACK_code(const char *fmt, ...);
void __SMACK_mod(const char *fmt, ...);
void __SMACK_decl(const char *fmt, ...);
void __SMACK_top_decl(const char *fmt, ...);

void __SMACK_assert(bool v) {
  __SMACK_code("assert {@} != 0;", v);
}

void __SMACK_assume(bool v) {
  __SMACK_code("assume {@} != 0;", v);
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
  D("function $add(p1:int, p2:int) returns (int) {p1 + p2}");
  D("function $sub(p1:int, p2:int) returns (int) {p1 - p2}");
  D("function $mul(p1:int, p2:int) returns (int) {p1 * p2}");
  D("function $sdiv(p1:int, p2:int) returns (int);");
  D("function $udiv(p1:int, p2:int) returns (int);");
  D("function $srem(p1:int, p2:int) returns (int);");
  D("function $urem(p1:int, p2:int) returns (int);");
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
  D("function $ult(p1:int, p2:int) returns (bool) {p1 < p2}");
  D("function $ugt(p1:int, p2:int) returns (bool) {p1 > p2}");
  D("function $ule(p1:int, p2:int) returns (bool) {p1 <= p2}");
  D("function $uge(p1:int, p2:int) returns (bool) {p1 >= p2}");
  D("function $slt(p1:int, p2:int) returns (bool) {p1 < p2}");
  D("function $sgt(p1:int, p2:int) returns (bool) {p1 > p2}");
  D("function $sle(p1:int, p2:int) returns (bool) {p1 <= p2}");
  D("function $sge(p1:int, p2:int) returns (bool) {p1 >= p2}");
  D("function $nand(p1:int, p2:int) returns (int);");
  D("function $max(p1:int, p2:int) returns (int);");
  D("function $min(p1:int, p2:int) returns (int);");
  D("function $umax(p1:int, p2:int) returns (int);");
  D("function $umin(p1:int, p2:int) returns (int);");
  D("function $i2b(i: int) returns (bool);");
  D("axiom (forall i:int :: $i2b(i) <==> i != 0);");
  D("axiom $i2b(0) == false;");
  D("function $b2i(b: bool) returns (int);");
  D("axiom $b2i(true) == 1;");
  D("axiom $b2i(false) == 0;");

  // Floating point
  D("type float;");
  D("function $fp(a:int) returns (float);");
  D("const $ffalse: float;");
  D("const $ftrue: float;");
  D("function $fadd(f1:float, f2:float) returns (float);");
  D("function $fsub(f1:float, f2:float) returns (float);");
  D("function $fmul(f1:float, f2:float) returns (float);");
  D("function $fdiv(f1:float, f2:float) returns (float);");
  D("function $frem(f1:float, f2:float) returns (float);");
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

  // Memory Model
  D("function $ptr(obj:int, off:int) returns (int) {obj + off}");
  D("function $obj(int) returns (int);");
  D("function $off(ptr:int) returns (int) {ptr}");

  D("const unique $NULL: int;");
  D("axiom $NULL == 0;");
  D("const $UNDEF: int;");

  D("function $pa(pointer: int, index: int, size: int) returns (int);");
  D("function $trunc(p: int, size: int) returns (int);");
  D("function $p2i(p: int) returns (int);");
  D("function $i2p(p: int) returns (int);");
  D("function $p2b(p: int) returns (bool);");
  D("function $b2p(b: bool) returns (int);");

  D("axiom (forall p:int, i:int, s:int :: {$pa(p,i,s)} $pa(p,i,s) == p + i * s);");
  D("axiom (forall p,s:int :: $trunc(p,s) == p);");

  D("axiom $b2p(true) == 1;");
  D("axiom $b2p(false) == 0;");
  D("axiom (forall i:int :: $p2b(i) <==> i != 0);");
  D("axiom $p2b(0) == false;");
  D("axiom (forall i:int :: $p2i(i) == i);");
  D("axiom (forall i:int :: $i2p(i) == i);");

  // Memory debugging symbols
  D("type $mop;");
  D("procedure boogie_si_record_mop(m: $mop);");
  D("procedure boogie_si_record_int(i: int);");
  D("const $MOP: $mop;");
  
  D("const $GLOBALS_BOTTOM: int;");
  D("function $isExternal(p: int) returns (bool) { p < $GLOBALS_BOTTOM - 32768 }");
  
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
    "ensures n >= 0 ==> (forall q: int :: {$obj(q)} p <= q && q < p+n ==> $obj(q) == p);");

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
    "ensures n >= 0 ==> (forall q: int :: {$obj(q)} p <= q && q < p+n ==> $obj(q) == p);");

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
    "ensures n >= 0 ==> (forall q: int :: {$obj(q)} p <= q && q < p+n ==> $obj(q) == p);");

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
    "ensures n >= 0 ==> (forall q: int :: {$obj(q)} p <= q && q < p+n ==> $obj(q) == p);");
#endif

  D("function $ev(p: int, i: int) returns (int);");

#undef D
}

#endif /*SMACK_H_*/
