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
const string SmackRep2dMem::STATIC = "$static";
const string SmackRep2dMem::EXTERN = "$extern";

vector<Decl*> SmackRep2dMem::globalDecl(const llvm::Value* v) {
  using namespace llvm;
  vector<Decl*> decls;
  vector<const Attr*> ax;
  string name = id(v);
  
  if (const GlobalVariable* g = dyn_cast<const GlobalVariable>(v)) {  
    if (g->hasInitializer()) {
      const llvm::Constant* init = g->getInitializer();
      unsigned numElems = numElements(init);
      if (numElems > 1)
        ax.push_back(Attr::attr("count",numElems));  
      addInit(getRegion(g), g, init);
    } else {
      decls.push_back(Decl::axiom(declareIsExternal(Expr::id(name))));
    }
  }
  decls.push_back(Decl::constant(name, REF_TYPE, ax, true));
  decls.push_back(Decl::axiom(Expr::fn(SmackRep2dMem::STATIC, Expr::id(name))));
  return decls;
}

const Expr* SmackRep2dMem::declareIsExternal(const Expr* e) {
  return Expr::fn(SmackRep2dMem::EXTERN, ptr2ref(e));
}

vector<string> SmackRep2dMem::getModifies() {
  vector<string> mods = SmackRep::getModifies();
  mods.push_back("$Alloc");
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

const Expr* SmackRep2dMem::trunc(const llvm::Value* v, llvm::Type* t) {
  assert(t->isIntegerTy() && "TODO: implement truncate for non-integer types.");
  if (isBool(t))
    return Expr::fn("$p2b",expr(v));
  else
    return Expr::fn(TRUNC,expr(v),lit(t->getPrimitiveSizeInBits()));
}

const string SmackRep2dMem::POINTERS =
  "// SMACK 2D Memory Model\n"
  "\n"
  "type $ref;\n"
  "type $ptr;\n"
  "\n"
  "function $ptr($ref, int) returns ($ptr);\n"
  "function $static($ref) returns (bool);\n"
  "function $extern($ref) returns (bool);\n"
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
  "axiom(forall r:$ref :: $static(r) ==> !$extern(r));\n"
  "const $UNDEF: $ptr;\n"
  "\n"
  "function $pa(pointer: $ptr, index: int, size: int) returns ($ptr);\n"
  "function $trunc(p: $ptr, size: int) returns ($ptr);\n"
  "function $p2i(p: $ptr) returns ($ptr);\n"
  "function $i2p(p: $ptr) returns ($ptr);\n"
  "function $p2b(p: $ptr) returns (bool);\n"
  "function $b2p(b: bool) returns ($ptr);\n"
  "\n"
  "axiom (forall p:$ptr, i:int, s:int :: {$pa(p,i,s)} $pa(p,i,s) == $ptr($obj(p), $off(p) + i * s));\n"
  "axiom (forall p:$ptr, i:int, s:int :: {$pa(p,i,s)} $obj($pa(p,i,s)) == $obj(p));\n"
  "axiom (forall p:$ptr, s:int :: $trunc(p,s) == p);\n"
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
  
  if (false)
    return
      "procedure $malloc(n: int) returns (p: $ptr)\n"
      "modifies $Alloc;\n"
      "{\n"
      "  assume !$static($obj(p));\n"
      "  assume $Alloc[$obj(p)] == $UNALLOCATED;\n"
      "  assume $off(p) == 0;\n"
      "  $Alloc[$obj(p)] := $ALLOCATED;\n"
      "}\n";
  else
    return
      "procedure $malloc(n: int) returns (p: $ptr);\n"
      "modifies $Alloc;\n"
      "ensures old($Alloc)[$obj(p)] == $UNALLOCATED;\n"
      "ensures $Alloc[$obj(p)] == $ALLOCATED;\n"
      "ensures !$static($obj(p));\n"
      "ensures $off(p) == 0;\n"
      "ensures (forall r: $ref :: {$Alloc[r]} r != $obj(p) ==> $Alloc[r] == old($Alloc)[r]);\n";
}

string SmackRep2dMem::freeProc() {
  if (false)
    return
      "procedure $free(p: $ptr)\n"
      "modifies $Alloc;\n"
      "{\n"
      "  $Alloc[$obj(p)] := $UNALLOCATED;\n"
      "}\n";
  else
    return
      "procedure $free(p: $ptr);\n"
      "modifies $Alloc;\n"
      "ensures $Alloc[$obj(p)] == $UNALLOCATED;\n"
      "ensures (forall r: $ref :: {$Alloc[r]} r != $obj(p) ==> $Alloc[r] == old($Alloc)[r]);\n";
}

string SmackRep2dMem::allocaProc() {
  if (false)
    return
      "procedure $alloca(n: int) returns (p: $ptr)\n"
      "modifies $Alloc;\n"
      "{\n"
      "  assume !$static($obj(p));\n"
      "  assume $Alloc[$obj(p)] == $UNALLOCATED;\n"
      "  assume $off(p) == 0;\n"
      "  $Alloc[$obj(p)] := $ALLOCATED;\n"
      "}\n";
  else
    return
      "procedure $alloca(n: int) returns (p: $ptr);\n"
      "modifies $Alloc;\n"
      "ensures old($Alloc)[$obj(p)] == $UNALLOCATED;\n"
      "ensures $Alloc[$obj(p)] == $ALLOCATED;\n"
      "ensures !$static($obj(p));\n"
      "ensures $off(p) == 0;\n"
      "ensures (forall r: $ref :: {$Alloc[r]} r != $obj(p) ==> $Alloc[r] == old($Alloc)[r]);\n";
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

string SmackRep2dMem::memsetProc(int dstReg) {
  stringstream s;
  s << "procedure $memset." << dstReg;
  s << "(dest: $ptr, val: $ptr, len: $ptr, align: $ptr, isvolatile: bool);" << endl;
  s << "modifies " << memReg(dstReg) << ";" << endl;
  s << "ensures (forall x:$ptr :: $obj(x) == $obj(dest)" << endl
    << "  && $off(dest) <= $off(x) && $off(x) < $off(dest) + $off(len)" << endl
    << "  ==> "
    << memReg(dstReg) << "[x] == $off(val));"
    << endl;
  s << "ensures (forall x:$ptr :: !($obj(x) == $obj(dest)" << endl
    << "  && $off(dest) <= $off(x) && $off(x) < $off(dest) + $off(len))" << endl
    << "  ==> "
    << memReg(dstReg) << "[x] == old("
    << memReg(dstReg) << ")[x]);" << endl;
  return s.str();
}


} // namespace smack
