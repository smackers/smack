//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SmackRep2dMem.h"
#include "smack/SmackOptions.h"

namespace smack {

const string SmackRep2dMem::PTR_TYPE = "$ptr";
const string SmackRep2dMem::REF_TYPE = "$ref";

vector<const Decl*> SmackRep2dMem::globalDecl(const llvm::Value* g) {
  addStaticInit(g);

  vector<const Decl*> decls;
  string name = id(g);
  decls.push_back(Decl::constant(name, REF_TYPE, true));
  decls.push_back(Decl::axiom(Expr::fn(SmackRep::STATIC, Expr::id(name))));
  return decls;
}

vector<string> SmackRep2dMem::getModifies() {
  vector<string> mods = SmackRep::getModifies();
  mods.push_back(ALLOC);
  return mods;
}

string SmackRep2dMem::getPtrType() {
  return PTR_TYPE;
}

const Expr* SmackRep2dMem::ptr2ref(const Expr* e) {
  return Expr::fn(OBJ, e);
}

const Expr* SmackRep2dMem::ptr2val(const Expr* e) {
  return Expr::fn(OFF, e);
}

const Expr* SmackRep2dMem::val2ptr(const Expr* e) {
  return Expr::fn(PTR, NUL, e);
}

const Expr* SmackRep2dMem::ref2ptr(const Expr* e) {
  return Expr::fn(PTR, e, Expr::lit(0));
}

const string SmackRep2dMem::POINTERS =
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
  "var $Alloc: [$ref] $name;\n"
  "\n"
  "const unique $NULL: $ref;\n"
  "axiom $static($NULL);\n"
  "const $UNDEF: $ptr;\n"
  "\n"
  "function $pa(pointer: $ptr, index: int, size: int) returns ($ptr);\n"
  "function $trunc(p: $ptr) returns ($ptr);\n"
  "function $p2i(p: $ptr) returns ($ptr);\n"
  "function $i2p(p: $ptr) returns ($ptr);\n"
  "function $p2b(p: $ptr) returns (bool);\n"
  "function $b2p(b: bool) returns ($ptr);\n"
  "\n"
  "axiom (forall p:$ptr, i:int, s:int :: {$pa(p,i,s)} $pa(p,i,s) == $ptr($obj(p), $off(p) + i * s));\n"
  "axiom (forall p:$ptr, i:int, s:int :: {$pa(p,i,s)} $obj($pa(p,i,s)) == $obj(p));\n"
  "axiom (forall p:$ptr :: $trunc(p) == p);\n"
  "\n"
  "axiom $b2p(true) == $ptr($NULL,1);\n"
  "axiom $b2p(false) == $ptr($NULL,0);\n"
  "\n"
  "axiom (forall r:$ref, i:int :: $p2b($ptr(r,i)) <==> i != 0);\n"
  "axiom $p2b($ptr($NULL,0)) == false;\n"
  "axiom (forall r:$ref, i:int :: $p2i($ptr(r,i)) == $ptr($NULL,i));\n"
  "axiom (forall i:int :: (exists r:$ref :: $i2p($ptr($NULL,i)) == $ptr(r,i)));\n";

string SmackRep2dMem::memoryModel() {
  return POINTERS;
}

string SmackRep2dMem::mallocProc() {
  stringstream s;
  
  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $malloc(obj_size: int) returns (new: int)" << endl;
    s << "  modifies $Alloc;" << endl;
    s << "  requires obj_size > 0;" << endl;
    s << "{" << endl;
    s << "  assume $Alloc[$obj(new)] = $UNALLOCATED;" << endl;
    s << "  assume !$static($obj(new));" << endl;
    s << "  assume $off(new) == 0;" << endl;
    s << "  assume $size($obj(new)) == obj_size;" << endl;
    s << "  $Alloc[$obj(new)] := $ALLOCATED;" << endl;
    s << "}" << endl;
  } else {
    s << "procedure $malloc(obj_size: int) returns (new: $ptr);" << endl;
    s << "modifies $Alloc;" << endl;
    s << "ensures old($Alloc)[$obj(new)] == $UNALLOCATED && $Alloc[$obj(new)] == $ALLOCATED;" << endl;
    s << "ensures !$static($obj(new));" << endl;
    s << "ensures $off(new) == 0;" << endl;
    s << "ensures $size($obj(new)) == obj_size;" << endl;
    s << "ensures (forall x_obj:$ref :: {$Alloc[x_obj]} x_obj == $obj(new) || old($Alloc)[x_obj] == $Alloc[x_obj]);" << endl;
  }  
  return s.str();
}

string SmackRep2dMem::freeProc() {
  stringstream s;
  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $free(pointer: $ptr)" << endl;
    s << "  modifies $Alloc;" << endl;
    s << "  requires $ALLOC[$obj(pointer)] == $ALLOCATED;" << endl;
    s << "  // requires !$static($obj(pointer);" << endl;
    s << "  requires $off(pointer) == 0;" << endl;
    s << "{" << endl;
    s << "  $Alloc[$obj(new)] := $UNALLOCATED;" << endl;
    s << "}" << endl;
  } else {   
    s << "procedure $free(pointer: $ptr);" << endl;
    s << "modifies $Alloc;" << endl;
    s << "requires $Alloc[$obj(pointer)] == $ALLOCATED;" << endl;
    s << "// requires !$static($obj(pointer));" << endl;
    s << "requires $off(pointer) == 0;" << endl;
    s << "ensures $Alloc[$obj(pointer)] != $UNALLOCATED;" << endl;
    s << "ensures (forall x:$ref :: {$Alloc[x]} $obj(pointer) == x || old($Alloc)[x] == $Alloc[x]);" << endl;
  }
  return s.str();
}

string SmackRep2dMem::allocaProc() {
  stringstream s;
  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $alloca(obj_size: int) returns (new: $ptr)" << endl;
    s << "  modifies $Alloc;" << endl;
    s << "  requires obj_size > 0;" << endl;
    s << "{" << endl;
    s << "  assume $Alloc[$obj(new)] == $UNALLOCATED;" << endl;
    s << "  assume !$static($obj(new));" << endl;
    s << "  assume $off(new) == 0;" << endl;
    s << "  assume $size($obj(new)) == obj_size;" << endl;
    s << "  $Alloc[$obj(new)] := $ALLOCATED;" << endl;
    s << "}" << endl;
  } else {   
    s << "procedure $alloca(obj_size: int) returns (new: $ptr);" << endl;
    s << "modifies $Alloc;" << endl;
    s << "ensures old($Alloc)[$obj(new)] == $UNALLOCATED && $Alloc[$obj(new)] == $ALLOCATED;" << endl;
    s << "ensures !$static($obj(new));" << endl;
    s << "ensures $off(new) == 0;" << endl;
    s << "ensures $size($obj(new)) == obj_size;" << endl;
    s << "ensures (forall x_obj:$ref :: {$Alloc[x_obj]} x_obj == $obj(new) || old($Alloc)[x_obj] == $Alloc[x_obj]);" << endl;
  }
  return s.str();
}

string SmackRep2dMem::memcpyProc(int dstReg, int srcReg) {
  stringstream s;
  s << "procedure $memcpy." << dstReg << "." << srcReg;
  s << "(dest: $ptr, src: $ptr, len: $ptr, align: $ptr, isvolatile: bool);" << endl;
  s << "modifies " << memReg(dstReg) << ";" << endl;
  s << "ensures (forall x:$ptr :: $obj(x) == $obj(dest)" << endl
    << "  && $off(dest) <= $off(x) && $off(x) < $off(dest) + $off(len)" << endl
    << "  ==> " 
    << memReg(dstReg) << "[x] == old(" 
    << memReg(srcReg) << ")[$ptr($obj(src),$off(src) - $off(dest) + $off(x))]);" 
    << endl;
  s << "ensures (forall x:$ptr :: !($obj(x) == $obj(dest)" << endl
    << "  && $off(dest) <= $off(x) && $off(x) < $off(dest) + $off(len))" << endl
    << "  ==> "
    << memReg(dstReg) << "[x] == old(" 
    << memReg(dstReg) << ")[x]);" << endl;
  return s.str();
}


} // namespace smack

