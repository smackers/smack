// SMACK-PRELUDE-BEGIN

// SMACK Memory Model

type $ref;
type $ptr;

const unique $NULL: $ref;
const $UNDEF: $ptr;

function $ptr($ref, int) returns ($ptr);
function $size($ref) returns (bv32);
function $obj($ptr) returns ($ref);
function $off($ptr) returns (bv32);

axiom(forall x:$ptr :: {$obj(x)}{$off(x)} x == $ptr($obj(x), $off(x)));
axiom(forall x_obj:$ref, x_off:bv32 :: {$ptr(x_obj, x_off)} x_obj == $obj($ptr(x_obj, x_off)));
axiom(forall x_obj:$ref, x_off:bv32 :: {$ptr(x_obj, x_off)} x_off == $off($ptr(x_obj, x_off)));

type $name;
const unique $UNALLOCATED: $name;
const unique $ALLOCATED: $name;
var Mem: [$ptr] $ptr;
var $Alloc: [$ref] $name;

procedure $alloca(obj_size: bv32) returns (new:$ptr);
modifies $Alloc;
ensures old($Alloc)[$obj(new)] == $UNALLOCATED && $Alloc[$obj(new)] == $ALLOCATED;
ensures $off(new) == 0bv32;
ensures $obj(new) != $NULL;
ensures $size($obj(new)) == obj_size;
ensures (forall x_obj:$ref :: {$Alloc[x_obj]} x_obj == $obj(new) || old($Alloc)[x_obj] == $Alloc[x_obj]);

procedure $malloc(obj_size: bv32) returns (new:$ptr);
modifies $Alloc;
ensures old($Alloc)[$obj(new)] == $UNALLOCATED && $Alloc[$obj(new)] == $ALLOCATED;
ensures $off(new) == 0bv32;
ensures $obj(new) != $NULL;
ensures $size($obj(new)) == obj_size;
ensures (forall x_obj:$ref :: {$Alloc[x_obj]} x_obj == $obj(new) || old($Alloc)[x_obj] == $Alloc[x_obj]);

procedure $free(pointer: $ptr);
modifies $Alloc;
requires $Alloc[$obj(pointer)] == $ALLOCATED;
requires $off(pointer) == 0bv32;
ensures $Alloc[$obj(pointer)] != $UNALLOCATED;
ensures (forall x:$ref :: {$Alloc[x]} $obj(pointer) == x || old($Alloc)[x] == $Alloc[x]);

// SMACK Arithmetic Predicates

function {:bvbuiltin "bvadd"} $add(p1:bv32, p2:bv32) returns (bv32);
function {:bvbuiltin "bvsub"} $sub(p1:bv32, p2:bv32) returns (bv32);
function {:bvbuiltin "bvmul"} $mul(p1:bv32, p2:bv32) returns (bv32);
function $sdiv(p1:bv32, p2:bv32) returns (bv32);
function $udiv(p1:bv32, p2:bv32) returns (bv32);
function $srem(p1:bv32, p2:bv32) returns (bv32);
function $and(p1:bv32, p2:bv32) returns (bv32);
function $or(p1:bv32, p2:bv32) returns (bv32);
function $xor(p1:bv32, p2:bv32) returns (bv32);
function $lshr(p1:bv32, p2:bv32) returns (bv32);
function $ashr(p1:bv32, p2:bv32) returns (bv32);
function $shl(p1:bv32, p2:bv32) returns (bv32);
function {:bvbuiltin "bvult"} $ult(p1:bv32, p2:bv32) returns (bool);
function {:bvbuiltin "bvugt"} $ugt(p1:bv32, p2:bv32) returns (bool);
function {:bvbuiltin "bvule"} $ule(p1:bv32, p2:bv32) returns (bool);
function {:bvbuiltin "bvuge"} $uge(p1:bv32, p2:bv32) returns (bool);
function {:bvbuiltin "bvslt"} $slt(p1:bv32, p2:bv32) returns (bool);
function {:bvbuiltin "bvsgt"} $sgt(p1:bv32, p2:bv32) returns (bool);
function {:bvbuiltin "bvsle"} $sle(p1:bv32, p2:bv32) returns (bool);
function {:bvbuiltin "bvsge"} $sge(p1:bv32, p2:bv32) returns (bool);

function $pa(pointer: $ptr, offset: bv32, size: bv32) returns ($ptr);
function $trunc(p:$ptr) returns ($ptr);
function $p2i(p: $ptr) returns ($ptr);
function $p2b(p: $ptr) returns (bool);
function $b2p(b: bool) returns ($ptr);
function $i2b(i: bv32) returns (bool);
function $b2i(b: bool) returns (bv32);

// SMACK Arithmetic Axioms

axiom $and(0bv32,0bv32) == 0bv32;
axiom $and(0bv32,1bv32) == 0bv32;
axiom $and(1bv32,0bv32) == 0bv32;
axiom $and(1bv32,1bv32) == 1bv32;

axiom $or(0bv32,0bv32) == 0bv32;
axiom $or(0bv32,1bv32) == 1bv32;
axiom $or(1bv32,0bv32) == 1bv32;
axiom $or(1bv32,1bv32) == 1bv32;

axiom $xor(0bv32,0bv32) == 0bv32;
axiom $xor(0bv32,1bv32) == 1bv32;
axiom $xor(1bv32,0bv32) == 1bv32;
axiom $xor(1bv32,1bv32) == 0bv32;

axiom (forall p:$ptr, o:bv32, s:bv32 :: {$pa(p,o,s)} $pa(p,o,s) == $ptr($obj(p), $off(p) + o * s));
axiom (forall p:$ptr, o:bv32, s:bv32 :: {$pa(p,o,s)} $obj($pa(p,o,s)) == $obj(p));
axiom (forall p:$ptr :: $trunc(p) == p);

axiom $b2i(true) == 1bv32;
axiom $b2i(false) == 0bv32;
axiom $b2p(true) == $ptr($NULL,1bv32);
axiom $b2p(false) == $ptr($NULL,0bv32);

axiom (forall i:bv32 :: $i2b(i) <==> i != 0bv32);
axiom $i2b(0bv32) == false;
axiom (forall r:$ref, i:bv32 :: $p2b($ptr(r,i)) <==> i != 0bv32);
axiom $p2b($ptr($NULL,0bv32)) == false;
axiom (forall r:$ref, i:bv32 :: $p2i($ptr(r,i)) == $ptr($NULL,i));

// SMACK Library Procedures

procedure __SMACK_nondet() returns (p: $ptr);
procedure __SMACK_nondetInt() returns (p: $ptr);
ensures $obj(p) == $NULL;

procedure __VERIFIER_nondet_int#0() returns (p: $ptr);
ensures $obj(p) == $NULL;

procedure __SMACK_assert(p: $ptr);
procedure __SMACK_assume(p: $ptr);

procedure boogie_si_record_int(i: bv32);
procedure boogie_si_record_obj(o: $ref);
procedure boogie_si_record_ptr(p: $ptr);

// C/C++ Library Procedures

procedure printf#1(p1:$ptr) returns (ret:$ptr);
procedure printf#2(p1:$ptr, p2:$ptr) returns (ret:$ptr);
procedure printf#3(p1:$ptr, p2:$ptr, p3:$ptr) returns (ret:$ptr);
procedure printf#4(p1:$ptr, p2:$ptr, p3:$ptr, p4:$ptr) returns (ret:$ptr);
procedure printf#5(p1:$ptr, p2:$ptr, p3:$ptr, p4:$ptr, p5:$ptr) returns (ret:$ptr);

// SMACK-PRELUDE-END

