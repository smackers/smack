//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SmackRepFlatMem.h"
#include "smack/SmackOptions.h"

namespace smack {

const string SmackRepFlatMem::CURRADDR = "$CurrAddr";
const string SmackRepFlatMem::PTR_TYPE = "int";
  
vector<const Decl*> SmackRepFlatMem::globalDecl(const llvm::Value* g) {
  addStaticInit(g);

  vector<const Decl*> decls;
  string name = id(g);
  decls.push_back(Decl::constant(name, getPtrType(), true));

  unsigned size;
  
  // NOTE: all global variables have pointer type in LLVM
  if (g->getType()->isPointerTy()) {
    llvm::PointerType *t = (llvm::PointerType*) g->getType();
    
    // in case we can determine the size of the element type ...
    if (t->getElementType()->isSized())
      size = storageSize(t->getElementType());
    
    // otherwise (e.g. for function declarations), use a default size
    else
      size = 1024;
    
  } else
    size = storageSize(g->getType());

  globalsTop -= size;

  decls.push_back(Decl::axiom(
                    Expr::eq(Expr::id(name), Expr::lit(globalsTop))));
  // Expr::fn("$slt",
  //     Expr::fn(SmackRep::ADD, Expr::id(name), Expr::lit(1024)),
  //     Expr::lit(globalsTop)) ));
  return decls;
}

vector<string> SmackRepFlatMem::getModifies() {
  vector<string> mods = SmackRep::getModifies();
  mods.push_back(ALLOC);
  mods.push_back(CURRADDR);
  return mods;
}

string SmackRepFlatMem::getPtrType() {
  return PTR_TYPE;
}

const Expr* SmackRepFlatMem::ptr2ref(const Expr* e) {
  return e;
}

const Expr* SmackRepFlatMem::ptr2val(const Expr* e) {
  return e;
}

const Expr* SmackRepFlatMem::val2ptr(const Expr* e) {
  return e;
}

const Expr* SmackRepFlatMem::ref2ptr(const Expr* e) {
  return e;
}
  
const string SmackRepFlatMem::POINTERS =
  "// SMACK Flat Memory Model\n"
  "\n"
  "function $ptr(obj:int, off:int) returns (int) {obj + off}\n"
  "function $size(int) returns (int);\n"
  "function $obj(int) returns (int);\n"
  "function $off(ptr:int) returns (int) {ptr}\n"
  "\n"
  "var $Alloc: [int] bool;\n"
  "var $CurrAddr:int;\n"
  "\n"
  "const unique $NULL: int;\n"
  "axiom $NULL == 0;\n"
  "const $UNDEF: int;\n"
  "\n"
  "function $pa(pointer: int, index: int, size: int) returns (int);\n"
  "function $trunc(p: int) returns (int);\n"
  "function $p2i(p: int) returns (int);\n"
  "function $i2p(p: int) returns (int);\n"
  "function $p2b(p: int) returns (bool);\n"
  "function $b2p(b: bool) returns (int);\n"
  "\n"
  "axiom (forall p:int, i:int, s:int :: {$pa(p,i,s)} $pa(p,i,s) == p + i * s);\n"
  "axiom (forall p:int :: $trunc(p) == p);\n"
  "\n"
  "axiom $b2p(true) == 1;\n"
  "axiom $b2p(false) == 0;\n"
  "axiom (forall i:int :: $p2b(i) <==> i != 0);\n"
  "axiom $p2b(0) == false;\n"
  "axiom (forall i:int :: $p2i(i) == i);\n"
  "axiom (forall i:int :: $i2p(i) == i);\n";

string SmackRepFlatMem::memoryModel() {
  return POINTERS;
}

string SmackRepFlatMem::mallocProc() {
  stringstream s;
  
  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $malloc(obj_size: int) returns (new: int)" << endl;
    s << "  modifies $CurrAddr, $Alloc;" << endl;
    s << "  requires obj_size > 0;" << endl;
    s << "{" << endl;
    s << "  assume $CurrAddr > 0;" << endl;
    s << "  new := $CurrAddr;" << endl;
    s << "  $CurrAddr := $CurrAddr + obj_size;" << endl;
    s << "  $Alloc[new] := true;" << endl;
    s << "}" << endl;
  } else {
    s << "procedure $malloc(obj_size: int) returns (new: int);" << endl;
    s << "modifies $CurrAddr, $Alloc;" << endl;
    s << "requires obj_size > 0;" << endl;
    s << "ensures 0 < old($CurrAddr);" << endl;
    s << "ensures new == old($CurrAddr);" << endl;
    s << "ensures $CurrAddr > old($CurrAddr) + obj_size;" << endl;
    s << "ensures $size(new) == obj_size;" << endl;
    s << "ensures (forall x:int :: new <= x && x < new + obj_size ==> $obj(x) == new);" << endl;
    s << "ensures $Alloc[new];" << endl;
    s << "ensures (forall x:int :: {$Alloc[x]} x == new || old($Alloc)[x] == $Alloc[x]);" << endl;;
  }  
  return s.str();
}

string SmackRepFlatMem::freeProc() {
  stringstream s;
  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $free(pointer: int)" << endl;
    s << "  modifies $Alloc;" << endl;
    s << "  // requires $Alloc[pointer];" << endl;
    s << "  // requires $obj(pointer) == pointer;" << endl;
    s << "{" << endl;
    s << "  $Alloc[pointer] := false;" << endl;
    s << "}" << endl;
  } else {
    s << "procedure $free(pointer: int);" << endl;
    s << "modifies $Alloc;" << endl;
    s << "requires $Alloc[pointer];" << endl;
    s << "requires $obj(pointer) == pointer;" << endl;
    s << "ensures !$Alloc[pointer];" << endl;
    s << "ensures (forall x:int :: {$Alloc[x]} x == pointer || old($Alloc)[x] == $Alloc[x]);" << endl;
  }
  return s.str();
}

string SmackRepFlatMem::allocaProc() {
  stringstream s;
  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $alloca(obj_size: int) returns (new: int)" << endl;
    s << "  modifies $CurrAddr, $Alloc;" << endl;
    s << "  requires obj_size > 0;" << endl;
    s << "{" << endl;
    s << "  assume $CurrAddr > 0;" << endl;
    s << "  new := $CurrAddr;" << endl;
    s << "  $CurrAddr := $CurrAddr + obj_size;" << endl;
    s << "  $Alloc[new] := true;" << endl;
    s << "}" << endl;
  } else {
    s << "procedure $alloca(obj_size: int) returns (new: int);" << endl;
    s << "modifies $CurrAddr, $Alloc;" << endl;
    s << "requires obj_size > 0;" << endl;
    s << "ensures 0 < old($CurrAddr);" << endl;
    s << "ensures new == old($CurrAddr);" << endl;
    s << "ensures $CurrAddr > old($CurrAddr) + obj_size;" << endl;
    s << "ensures $size(new) == obj_size;" << endl;
    s << "ensures (forall x:int :: new <= x && x < new + obj_size ==> $obj(x) == new);" << endl;
    s << "ensures $Alloc[new];" << endl;
    s << "ensures (forall x:int :: {$Alloc[x]} x == new || old($Alloc)[x] == $Alloc[x]);" << endl;
  }
  return s.str();
}

string SmackRepFlatMem::memcpyProc(int dstReg, int srcReg) {
  stringstream s;
  s << "procedure $memcpy." << dstReg << "." << srcReg;
  s << "(dest: int, src: int, len: int, align: int, isvolatile: bool);" << endl;
  s << "modifies " << memReg(dstReg) << ";" << endl;
  s << "ensures (forall x:int :: dest <= x && x < dest + len ==> " 
    << memReg(dstReg) << "[x] == old(" << memReg(srcReg) << ")[src - dest + x]);" 
    << endl;
  s << "ensures (forall x:int :: !(dest <= x && x < dest + len) ==> "
    << memReg(dstReg) << "[x] == old(" << memReg(dstReg) << ")[x]);" << endl;
  return s.str();
}

} // namespace smack

