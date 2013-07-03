//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "SmackRep2dMem.h"

namespace smack {

const string SmackRep2dMem::PTR_TYPE = "$ptr";
const string SmackRep2dMem::REF_TYPE = "$ref";

vector<const Decl*> SmackRep2dMem::globalDecl(const llvm::Value* g) {
  vector<const Decl*> decls;
  string name = id(g);
  decls.push_back(Decl::constant(name, REF_TYPE, true));
  decls.push_back(Decl::axiom(Expr::fn(SmackRep::STATIC, Expr::id(name))));
  return decls;
}

vector<string> SmackRep2dMem::getModifies() {
  vector<string> mods = SmackRep::getModifies();
  mods.push_back(MEMORY);
  mods.push_back(ALLOC);
  return mods;
}

string SmackRep2dMem::getPtrType() {
  return PTR_TYPE;
}

string SmackRep2dMem::getPrelude() {
  return PRELUDE + SmackRep::getPrelude();
}

const string SmackRep2dMem::PRELUDE =
  "// SMACK 2D Memory Model\n"
  "\n"
  "type $ref;\n"
  "type $ptr;\n"
  "\n"
  "function $ptr($ref, int) returns ($ptr);\n"
  "function $static($ref) returns (bool);\n"
  "function $size($ref) returns (int);\n"
  "function $obj($ptr) returns ($ref);\n"
  "function $off($ptr) returns (int);\n"
  "\n"
  "axiom(forall x:$ptr :: {$obj(x)}{$off(x)} x == $ptr($obj(x), $off(x)));\n"
  "axiom(forall x_obj:$ref, x_off:int :: {$ptr(x_obj, x_off)} x_obj == $obj($ptr(x_obj, x_off)));\n"
  "axiom(forall x_obj:$ref, x_off:int :: {$ptr(x_obj, x_off)} x_off == $off($ptr(x_obj, x_off)));\n"
  "\n"
  "type $name;\n"
  "const unique $UNALLOCATED: $name;\n"
  "const unique $ALLOCATED: $name;\n"
  "var $Mem: [$ptr] $ptr;\n"
  "var $Alloc: [$ref] $name;\n"
  "\n"
  "const unique $NULL: $ref;\n"
  "axiom $static($NULL);\n"
  "const $UNDEF: $ptr;\n"
  "\n"
  "procedure $malloc(obj_size: int) returns (new: $ptr);\n"
  "modifies $Alloc;\n"
  "ensures old($Alloc)[$obj(new)] == $UNALLOCATED && $Alloc[$obj(new)] == $ALLOCATED;\n"
  "ensures !$static($obj(new));\n"
  "ensures $off(new) == 0;\n"
  "ensures $size($obj(new)) == obj_size;\n"
  "ensures (forall x_obj:$ref :: {$Alloc[x_obj]} x_obj == $obj(new) || old($Alloc)[x_obj] == $Alloc[x_obj]);\n"
  "\n"
  "procedure $alloca(obj_size: int) returns (new: $ptr);\n"
  "modifies $Alloc;\n"
  "ensures old($Alloc)[$obj(new)] == $UNALLOCATED && $Alloc[$obj(new)] == $ALLOCATED;\n"
  "ensures !$static($obj(new));\n"
  "ensures $off(new) == 0;\n"
  "ensures $size($obj(new)) == obj_size;\n"
  "ensures (forall x_obj:$ref :: {$Alloc[x_obj]} x_obj == $obj(new) || old($Alloc)[x_obj] == $Alloc[x_obj]);\n"
  "\n"
  "procedure $free(pointer: $ptr);\n"
  "modifies $Alloc;\n"
  "requires $Alloc[$obj(pointer)] == $ALLOCATED;\n"
  "// requires !$static($obj(pointer));\n"
  "requires $off(pointer) == 0;\n"
  "ensures $Alloc[$obj(pointer)] != $UNALLOCATED;\n"
  "ensures (forall x:$ref :: {$Alloc[x]} $obj(pointer) == x || old($Alloc)[x] == $Alloc[x]);\n"
  "\n"
  "procedure $memcpy(dest:$ptr, src:$ptr, len:$ptr, align:$ptr, isvolatile:bool);\n"
  "modifies $Mem;\n"
  "ensures (forall x:$ptr :: $obj(x) == $obj(dest) && $off(dest) <= $off(x) && $off(x) < $off(dest) + $off(len) ==> $Mem[x] == old($Mem)[$ptr($obj(src),$off(src) - $off(dest) + $off(x))]);\n"
  "ensures (forall x:$ptr :: !($obj(x) == $obj(dest) && $off(dest) <= $off(x) && $off(x) < $off(dest) + $off(len)) ==> $Mem[x] == old($Mem)[x]);\n"
  "\n"
  "function $pa(pointer: $ptr, offset: int, size: int) returns ($ptr);\n"
  "function $trunc(p: $ptr) returns ($ptr);\n"
  "function $p2i(p: $ptr) returns ($ptr);\n"
  "function $i2p(p: $ptr) returns ($ptr);\n"
  "function $p2b(p: $ptr) returns (bool);\n"
  "function $b2p(b: bool) returns ($ptr);\n"
  "\n"
  "axiom (forall p:$ptr, o:int, s:int :: {$pa(p,o,s)} $pa(p,o,s) == $ptr($obj(p), $off(p) + o * s));\n"
  "axiom (forall p:$ptr, o:int, s:int :: {$pa(p,o,s)} $obj($pa(p,o,s)) == $obj(p));\n"
  "axiom (forall p:$ptr :: $trunc(p) == p);\n"
  "\n"
  "axiom $b2p(true) == $ptr($NULL,1);\n"
  "axiom $b2p(false) == $ptr($NULL,0);\n"
  "\n"
  "axiom (forall r:$ref, i:int :: $p2b($ptr(r,i)) <==> i != 0);\n"
  "axiom $p2b($ptr($NULL,0)) == false;\n"
  "axiom (forall r:$ref, i:int :: $p2i($ptr(r,i)) == $ptr($NULL,i));\n"
  "axiom (forall i:int :: (exists r:$ref :: $i2p($ptr($NULL,i)) == $ptr(r,i)));\n"
  "\n"
  "procedure __SMACK_nondet() returns (p: $ptr);\n"
  "procedure __SMACK_nondetInt() returns (p: $ptr);\n"
  "ensures $obj(p) == $NULL;\n";

} // namespace smack

