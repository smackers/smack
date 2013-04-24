// SMACK-PRELUDE-BEGIN

// SMACK Memory Model

type $ref;
type $ptr;

const unique $NULL: $ref;
const $UNDEF: $ptr;

function $ptr($ref, int) returns ($ptr);
function $size($ref) returns (int);
function $obj($ptr) returns ($ref);
function $off($ptr) returns (int);

axiom(forall x:$ptr :: {$obj(x)}{$off(x)} x == $ptr($obj(x), $off(x)));
axiom(forall x_obj:$ref, x_off:int :: {$ptr(x_obj, x_off)} x_obj == $obj($ptr(x_obj, x_off)));
axiom(forall x_obj:$ref, x_off:int :: {$ptr(x_obj, x_off)} x_off == $off($ptr(x_obj, x_off)));

type $name;
const unique $UNALLOCATED: $name;
const unique $ALLOCATED: $name;
var $Mem: [$ptr] $ptr;
var $Alloc: [$ref] $name;

procedure $alloca(obj_size: int) returns (new: $ptr);
modifies $Alloc;
ensures old($Alloc)[$obj(new)] == $UNALLOCATED && $Alloc[$obj(new)] == $ALLOCATED;
ensures $off(new) == 0;
ensures $obj(new) != $NULL;
ensures $size($obj(new)) == obj_size;
ensures (forall x_obj:$ref :: {$Alloc[x_obj]} x_obj == $obj(new) || old($Alloc)[x_obj] == $Alloc[x_obj]);

procedure $malloc(obj_size: int) returns (new: $ptr);
modifies $Alloc;
ensures old($Alloc)[$obj(new)] == $UNALLOCATED && $Alloc[$obj(new)] == $ALLOCATED;
ensures $off(new) == 0;
ensures $obj(new) != $NULL;
ensures $size($obj(new)) == obj_size;
ensures (forall x_obj:$ref :: {$Alloc[x_obj]} x_obj == $obj(new) || old($Alloc)[x_obj] == $Alloc[x_obj]);

procedure $free(pointer: $ptr);
modifies $Alloc;
requires $Alloc[$obj(pointer)] == $ALLOCATED;
requires $off(pointer) == 0;
ensures $Alloc[$obj(pointer)] != $UNALLOCATED;
ensures (forall x:$ref :: {$Alloc[x]} $obj(pointer) == x || old($Alloc)[x] == $Alloc[x]);

// SMACK Arithmetic Predicates

function $add(p1:int, p2:int) returns (int) {p1 + p2}
function $sub(p1:int, p2:int) returns (int) {p1 - p2}
function $mul(p1:int, p2:int) returns (int) {p1 * p2}
function $sdiv(p1:int, p2:int) returns (int);
function $udiv(p1:int, p2:int) returns (int);
function $srem(p1:int, p2:int) returns (int);
function $and(p1:int, p2:int) returns (int);
function $or(p1:int, p2:int) returns (int);
function $xor(p1:int, p2:int) returns (int);
function $lshr(p1:int, p2:int) returns (int);
function $ashr(p1:int, p2:int) returns (int);
function $shl(p1:int, p2:int) returns (int);
function $ult(p1:int, p2:int) returns (bool) {p1 < p2}
function $ugt(p1:int, p2:int) returns (bool) {p1 > p2}
function $ule(p1:int, p2:int) returns (bool) {p1 <= p2}
function $uge(p1:int, p2:int) returns (bool) {p1 >= p2}
function $slt(p1:int, p2:int) returns (bool) {p1 < p2}
function $sgt(p1:int, p2:int) returns (bool) {p1 > p2}
function $sle(p1:int, p2:int) returns (bool) {p1 <= p2}
function $sge(p1:int, p2:int) returns (bool) {p1 >= p2}

function $pa(pointer: $ptr, offset: int, size: int) returns ($ptr);
function $trunc(p: $ptr) returns ($ptr);
function $p2i(p: $ptr) returns ($ptr);
function $p2b(p: $ptr) returns (bool);
function $b2p(b: bool) returns ($ptr);
function $i2b(i: int) returns (bool);
function $b2i(b: bool) returns (int);

// SMACK Arithmetic Axioms

axiom $and(0,0) == 0;
axiom $and(0,1) == 0;
axiom $and(1,0) == 0;
axiom $and(1,1) == 1;

axiom $or(0,0) == 0;
axiom $or(0,1) == 1;
axiom $or(1,0) == 1;
axiom $or(1,1) == 1;

axiom $xor(0,0) == 0;
axiom $xor(0,1) == 1;
axiom $xor(1,0) == 1;
axiom $xor(1,1) == 0;

axiom (forall p:$ptr, o:int, s:int :: {$pa(p,o,s)} $pa(p,o,s) == $ptr($obj(p), $off(p) + o * s));
axiom (forall p:$ptr, o:int, s:int :: {$pa(p,o,s)} $obj($pa(p,o,s)) == $obj(p));
axiom (forall p:$ptr :: $trunc(p) == p);

axiom $b2i(true) == 1;
axiom $b2i(false) == 0;
axiom $b2p(true) == $ptr($NULL,1);
axiom $b2p(false) == $ptr($NULL,0);

axiom (forall i:int :: $i2b(i) <==> i != 0);
axiom $i2b(0) == false;
axiom (forall r:$ref, i:int :: $p2b($ptr(r,i)) <==> i != 0);
axiom $p2b($ptr($NULL,0)) == false;
axiom (forall r:$ref, i:int :: $p2i($ptr(r,i)) == $ptr($NULL,i));

// SMACK Library Procedures

procedure __SMACK_nondet() returns (p: $ptr);
procedure __SMACK_nondetInt() returns (p: $ptr);
ensures $obj(p) == $NULL;

procedure __VERIFIER_nondet_int() returns (p: $ptr);
ensures $obj(p) == $NULL;

procedure __SMACK_assert(p: $ptr);
procedure __SMACK_assume(p: $ptr);

procedure boogie_si_record_int(i: int);
procedure boogie_si_record_obj(o: $ref);
procedure boogie_si_record_ptr(p: $ptr);

// SMACK-PRELUDE-END

