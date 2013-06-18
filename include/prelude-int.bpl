// SMACK-PRELUDE-BEGIN

// SMACK Memory Model

const $UNDEF: int;

// function $size(int) returns (int);
// type $name;
// const unique $UNALLOCATED: $name;
// const unique $ALLOCATED: $name;
var $Mem: [int] int;
var $CurrAddr:int;
var $Alloc: [int] bool;

procedure $malloc(obj_size: int) returns (new: int);
modifies $CurrAddr, $Alloc;
requires obj_size > 0;
ensures 0 < old($CurrAddr);
ensures new == old($CurrAddr);
ensures $CurrAddr > old($CurrAddr) + obj_size;
ensures $Alloc[new];
ensures (forall x:int :: {$Alloc[x]} x == new || old($Alloc)[x] == $Alloc[x]);

procedure $alloca(obj_size: int) returns (new: int);
modifies $CurrAddr, $Alloc;
requires obj_size > 0;
ensures 0 < old($CurrAddr);
ensures new == old($CurrAddr);
ensures $CurrAddr > old($CurrAddr) + obj_size;
ensures $Alloc[new];
ensures (forall x:int :: {$Alloc[x]} x == new || old($Alloc)[x] == $Alloc[x]);

procedure $free(pointer: int);
modifies $Alloc;
requires $Alloc[pointer];
ensures !$Alloc[pointer];
ensures (forall x:int :: {$Alloc[x]} x == pointer || old($Alloc)[x] == $Alloc[x]);

// SMACK Arithmetic Predicates

function $add(p1:int, p2:int) returns (int) {p1 + p2}
function $sub(p1:int, p2:int) returns (int) {p1 - p2}
function $mul(p1:int, p2:int) returns (int) {p1 * p2}
function $sdiv(p1:int, p2:int) returns (int);
function $udiv(p1:int, p2:int) returns (int);
function $srem(p1:int, p2:int) returns (int);
function $urem(p1:int, p2:int) returns (int);
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

function $pa(pointer: int, offset: int, size: int) returns (int);
function $trunc(p: int) returns (int);
function $p2i(p: int) returns (int);
function $i2p(p: int) returns (int);
function $p2b(p: int) returns (bool);
function $b2p(b: bool) returns (int);
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

axiom (forall p:int, o:int, s:int :: {$pa(p,o,s)} $pa(p,o,s) == p + o * s);
axiom (forall p:int :: $trunc(p) == p);

axiom $b2i(true) == 1;
axiom $b2i(false) == 0;
axiom $b2p(true) == 1;
axiom $b2p(false) == 0;

axiom (forall i:int :: $i2b(i) <==> i != 0);
axiom $i2b(0) == false;
axiom (forall i:int :: $p2b(i) <==> i != 0);
axiom $p2b(0) == false;
axiom (forall i:int :: $p2i(i) == i);
axiom (forall i:int :: $i2p(i) == i);

// SMACK Library Procedures

procedure __SMACK_nondet() returns (p: int);
procedure __SMACK_nondetInt() returns (p: int);

// procedure boogie_si_record_int(i: int);
// procedure boogie_si_record_obj(o: $ref);
// procedure boogie_si_record_ptr(p: $ptr);

// SMACK-PRELUDE-END

