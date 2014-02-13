//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "smack/SmackRepFlatMem.h"
#include "smack/SmackOptions.h"

namespace smack {

const string SmackRepFlatMem::CURRADDR = "$CurrAddr";
const string SmackRepFlatMem::BOTTOM = "$GLOBALS_BOTTOM";
const string SmackRepFlatMem::IS_EXT = "$isExternal";
const string SmackRepFlatMem::PTR_TYPE = "int";
  
vector<Decl*> SmackRepFlatMem::globalDecl(const llvm::Value* g) {
  addStaticInit(g);

  vector<Decl*> decls;
  string name = id(g);
  decls.push_back(Decl::constant(name, getPtrType(), true));
  
  if (((llvm::GlobalVariable*)g)->hasInitializer()) {
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

    bottom -= size;

    decls.push_back(Decl::axiom(Expr::eq(Expr::id(name),Expr::lit(bottom))));
    // Expr::fn("$slt",
    //     Expr::fn(SmackRep::ADD, Expr::id(name), Expr::lit(1024)),
    //     Expr::lit(bottom)) ));
    
  } else {
    // A global variable is external iff it has no initializer
    decls.push_back(Decl::axiom(declareIsExternal(Expr::id(name))));
  }

  return decls;
}

const Expr* SmackRepFlatMem::declareIsExternal(const Expr* e) {
  return Expr::fn(IS_EXT,e);
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
  stringstream s;
  s << POINTERS;
  s << "function " << IS_EXT << "(p: int) returns (bool) { p < " << bottom - 32768 << " }" << endl;
  s << "const " << BOTTOM << ": int;" << endl;
  s << "axiom " << BOTTOM << " == " << bottom << ";" << endl;
  return s.str();
}

string SmackRepFlatMem::mallocProc() {
  if (SmackOptions::MemoryModelImpls)
    return 
      "procedure $malloc(n: int) returns (p: int)\n"
      "modifies $CurrAddr, $Alloc;\n"
      "{\n"
      "  assume $CurrAddr > 0;\n"
      "  p := $CurrAddr;\n"
      "  assume n > 0 ==> $size(p) == n;\n"
      "  assume n <= 0 ==> $size(p) == 0;\n"
      "  $CurrAddr := $CurrAddr + $size(p) + 1;\n"
      "  $Alloc[p] := true;\n"
      "}\n";
  else    
    return
      "procedure $malloc(n: int) returns (p: int);\n"
      "modifies $CurrAddr, $Alloc;\n"
      "ensures n > 0 ==> $size(p) == n;\n"
      "ensures n <= 0 ==> $size(p) == 0;\n"
      "ensures p == old($CurrAddr);\n"
      "ensures $CurrAddr > old($CurrAddr);\n"
      "ensures n >= 0 ==> $CurrAddr >= old($CurrAddr) + n;\n"
      "ensures $Alloc[p];\n"
      "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
      "ensures n >= 0 ==> (forall q: int :: p <= q && q < p+n ==> $obj(q) == p);\n";
}

string SmackRepFlatMem::freeProc() {
  if (SmackOptions::MemoryModelImpls)
    return
      "procedure $free(p: int)\n"
      "modifies $Alloc;\n"
      "{\n"
      "  $Alloc[p] := false;\n"
      "}\n";  
  else
    return
      "procedure $free(p: int);\n"
      "modifies $Alloc;\n"
      "ensures !$Alloc[p];\n"
      "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n";
}

string SmackRepFlatMem::allocaProc() {
  if (SmackOptions::MemoryModelImpls)
    return 
      "procedure $alloca(n: int) returns (p: int)\n"
      "modifies $CurrAddr, $Alloc;\n"
      "{\n"
      "  assume $CurrAddr > 0;\n"
      "  p := $CurrAddr;\n"
      "  assume n > 0 ==> $size(p) == n;\n"
      "  assume n <= 0 ==> $size(p) == 0;\n"
      "  $CurrAddr := $CurrAddr + $size(p) + 1;\n"
      "  $Alloc[p] := true;\n"
      "}\n";
  else    
    return
      "procedure $alloca(n: int) returns (p: int);\n"
      "modifies $CurrAddr, $Alloc;\n"
      "ensures n > 0 ==> $size(p) == n;\n"
      "ensures n <= 0 ==> $size(p) == 0;\n"
      "ensures p == old($CurrAddr);\n"
      "ensures $CurrAddr > old($CurrAddr);\n"
      "ensures n >= 0 ==> $CurrAddr >= old($CurrAddr) + n;\n"
      "ensures $Alloc[p];\n"
      "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
      "ensures n >= 0 ==> (forall q: int :: p <= q && q < p+n ==> $obj(q) == p);\n";
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
