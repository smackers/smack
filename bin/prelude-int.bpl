//******** AXIOMS *********
type ref;
type name;
type ptr;
const unique null:ref;
function Ptr(ref, int) returns (ptr);
function Obj(ptr) returns (ref);
function Off(ptr) returns (int);

// Ptr, Obj, Off axioms
axiom(forall x:ptr :: {Obj(x)}{Off(x)} x == Ptr(Obj(x), Off(x)));
axiom(forall x_obj:ref, x_off:int :: {Ptr(x_obj, x_off)} x_obj == Obj(Ptr(x_obj, x_off)));
axiom(forall x_obj:ref, x_off:int :: {Ptr(x_obj, x_off)} x_off == Off(Ptr(x_obj, x_off)));

// Mutable
var Mem:[ptr]ptr;
var Alloc:[ref]name;

// Immutable
function Size(ref) returns (int);

// Undefined ptr value
var undef:ptr;

// Constants
const unique UNALLOCATED:name;
const unique ALLOCATED:name;

procedure __SMACK_alloca(obj_size:int) returns (new:ptr);
modifies Alloc;
ensures old(Alloc)[Obj(new)] == UNALLOCATED && Alloc[Obj(new)] == ALLOCATED;
ensures Off(new) == 0;
ensures Obj(new) != null;
ensures Size(Obj(new)) == obj_size;
ensures (forall x_obj:ref :: {Alloc[x_obj]} x_obj == Obj(new) || old(Alloc)[x_obj] == Alloc[x_obj]);

procedure __SMACK_malloc(obj_size:int) returns (new:ptr);
modifies Alloc;
ensures old(Alloc)[Obj(new)] == UNALLOCATED && Alloc[Obj(new)] == ALLOCATED;
ensures Off(new) == 0;
ensures Obj(new) != null;
ensures Size(Obj(new)) == obj_size;
ensures (forall x_obj:ref :: {Alloc[x_obj]} x_obj == Obj(new) || old(Alloc)[x_obj] == Alloc[x_obj]);

procedure __SMACK_free(pointer:ptr);
modifies Alloc;
requires Alloc[Obj(pointer)] == ALLOCATED;
requires Off(pointer) == 0;
ensures Alloc[Obj(pointer)] != UNALLOCATED;
ensures (forall x:ref :: {Alloc[x]} Obj(pointer) == x || old(Alloc)[x] == Alloc[x]);


// comparison operators procedures
procedure __SMACK_Proc_ICMP_EQ(a:ptr, b:ptr) returns (result:bool);
ensures result == (a == b);

procedure __SMACK_Proc_ICMP_NE(a:ptr, b:ptr) returns (result:bool);
ensures result == (a != b);

procedure __SMACK_Proc_ICMP_GE(a:ptr, b:ptr) returns (result:bool);
ensures result == (Off(a) >= Off(b));

procedure __SMACK_Proc_ICMP_LE(a:ptr, b:ptr) returns (result:bool);
ensures result == (Off(a) <= Off(b));

procedure __SMACK_Proc_ICMP_LT(a:ptr, b:ptr) returns (result:bool);
ensures result == (Off(a) < Off(b));

procedure __SMACK_Proc_ICMP_GT(a:ptr, b:ptr) returns (result:bool);
ensures result == (Off(a) > Off(b));


procedure __SMACK_Add(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null && Off(result) == Off(a) + Off(b);

procedure __SMACK_Sub(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null && Off(result) == Off(a) - Off(b);

procedure __SMACK_Mul(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null && Off(result) == Off(a) * Off(b);

procedure __SMACK_SDiv(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null;

procedure __SMACK_UDiv(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null;

procedure __SMACK_SRem(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null;

procedure __SMACK_URem(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null;

procedure __SMACK_And(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null;

procedure __SMACK_Or(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null;

procedure __SMACK_Xor(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null;

procedure __SMACK_LShr(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null;

procedure __SMACK_AShr(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null;

procedure __SMACK_Shl(a:ptr, b:ptr) returns (result:ptr);
ensures Obj(result) == null;

procedure __SMACK_Trunc(a:ptr) returns (result:ptr);
ensures result == a;

function __SMACK_PtrArith(pointer:ptr, offset:int, size:int) returns (result:ptr);
axiom(forall p:ptr, off:int, size:int :: {__SMACK_PtrArith(p, off, size)}
  __SMACK_PtrArith(p, off, size) == Ptr(Obj(p), Off(p) + off * size));

procedure __SMACK_BoolToInt(a:bool) returns (result:ptr);
ensures Obj(result) == null;
ensures (a && Off(result) != 0) || (!a && Off(result) == 0);

procedure __SMACK_isInt(x:ptr) returns (result:ptr);
ensures (Obj(x) == null && result != Ptr(null, 0)) || (Obj(x) != null && result == Ptr(null, 0));

procedure __SMACK_nondet() returns (x:ptr);

procedure __SMACK_nondetInt() returns (x:ptr);
ensures Obj(x) == null;

//**** HEADER END ****


