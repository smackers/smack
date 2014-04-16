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

Regex STRING_CONSTANT("^\\.str[0-9]*$");
  
vector<Decl*> SmackRepFlatMem::globalDecl(const llvm::Value* v) {
  using namespace llvm;
  vector<Decl*> decls;
  vector<const Attr*> ax;
  string name = id(v);
  
  if (const GlobalVariable* g = dyn_cast<const GlobalVariable>(v)) {
    if (g->hasInitializer()) {
      const Constant* init = g->getInitializer();
      unsigned numElems = numElements(init);
      unsigned size;
  
      // NOTE: all global variables have pointer type in LLVM
      if (g->getType()->isPointerTy()) {
        PointerType *t = (PointerType*) g->getType();
    
        // in case we can determine the size of the element type ...
        if (t->getElementType()->isSized())
          size = storageSize(t->getElementType());
    
        // otherwise (e.g. for function declarations), use a default size
        else
          size = 1024;
    
      } else
        size = storageSize(g->getType());

      bottom -= size;

      if (!g->hasName() || !STRING_CONSTANT.match(g->getName().str())) {
        if (numElems > 1)
          ax.push_back(Attr::attr("count",numElems));

        decls.push_back(Decl::axiom(Expr::eq(Expr::id(name),Expr::lit(bottom))));
        addInit(getRegion(g), expr(g), init);

        // Expr::fn("$slt",
        //     Expr::fn(SmackRep::ADD, Expr::id(name), Expr::lit(1024)),
        //     Expr::lit(bottom)) ));
      }
    
    } else {
      decls.push_back(Decl::axiom(declareIsExternal(Expr::id(name))));
    }
  }
  decls.push_back(Decl::constant(name, getPtrType(), ax, true));
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

const Expr* SmackRepFlatMem::trunc(const Expr* e, llvm::Type* t) {
  assert(t->isIntegerTy() && "TODO: implement truncate for non-integer types.");

  if (isBool(t))
    return Expr::fn(I2B,e);
  else
    return Expr::fn(TRUNC,e,lit(t->getPrimitiveSizeInBits()));
}
  
const string SmackRepFlatMem::POINTERS =
  "// SMACK Flat Memory Model\n"
  "\n"
  "function $ptr(obj:int, off:int) returns (int) {obj + off}\n"
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
  "function $trunc(p: int, size: int) returns (int);\n"
  "function $p2i(p: int) returns (int);\n"
  "function $i2p(p: int) returns (int);\n"
  "function $p2b(p: int) returns (bool);\n"
  "function $b2p(b: bool) returns (int);\n"
  "\n"
  "axiom (forall p:int, i:int, s:int :: {$pa(p,i,s)} $pa(p,i,s) == p + i * s);\n"
  "axiom (forall p,s:int :: $trunc(p,s) == p);\n"
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
      "  if (n > 0) {\n"
      "    $CurrAddr := $CurrAddr + n;\n"
      "  } else {\n"
      "    $CurrAddr := $CurrAddr + 1;\n"
      "  }\n"
      "  $Alloc[p] := true;\n"
      "}\n";
  else    
    return
      "procedure $malloc(n: int) returns (p: int);\n"
      "modifies $CurrAddr, $Alloc;\n"
      "ensures p > 0;\n"
      "ensures p == old($CurrAddr);\n"
      "ensures $CurrAddr > old($CurrAddr);\n"
      "ensures n >= 0 ==> $CurrAddr >= old($CurrAddr) + n;\n"
      "ensures $Alloc[p];\n"
      "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
      "ensures n >= 0 ==> (forall q: int :: {$obj(q)} p <= q && q < p+n ==> $obj(q) == p);\n";
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
      "  if (n > 0) {\n"
      "    $CurrAddr := $CurrAddr + n;\n"
      "  } else {\n"
      "    $CurrAddr := $CurrAddr + 1;\n"
      "  }\n"
      "  $Alloc[p] := true;\n"
      "}\n";
  else    
    return
      "procedure $alloca(n: int) returns (p: int);\n"
      "modifies $CurrAddr, $Alloc;\n"
      "ensures p > 0;\n"
      "ensures p == old($CurrAddr);\n"
      "ensures $CurrAddr > old($CurrAddr);\n"
      "ensures n >= 0 ==> $CurrAddr >= old($CurrAddr) + n;\n"
      "ensures $Alloc[p];\n"
      "ensures (forall q: int :: {$Alloc[q]} q != p ==> $Alloc[q] == old($Alloc[q]));\n"
      "ensures n >= 0 ==> (forall q: int :: {$obj(q)} p <= q && q < p+n ==> $obj(q) == p);\n";
}

string SmackRepFlatMem::memcpyProc(int dstReg, int srcReg) {
  stringstream s;

  if (SmackOptions::MemoryModelImpls) {
    s << "procedure $memcpy." << dstReg << "." << srcReg;
    s << "(dest: int, src: int, len: int, align: int, isvolatile: bool)" << endl;
    s << "modifies " << memReg(dstReg) << ";" << endl;
    s << "{" << endl;
    s << "  var $oldSrc: [" << getPtrType() << "] " << getPtrType() << ";" << endl;
    s << "  var $oldDst: [" << getPtrType() << "] " << getPtrType() << ";" << endl;
    s << "  $oldSrc := " << memReg(srcReg) << ";" << endl;
    s << "  $oldDst := " << memReg(dstReg) << ";" << endl;
    s << "  havoc " << memReg(dstReg) << ";" << endl;
    s << "  assume (forall x:int :: dest <= x && x < dest + len ==> " 
      << memReg(dstReg) << "[x] == $oldSrc[src - dest + x]);" << endl;
    s << "  assume (forall x:int :: !(dest <= x && x < dest + len) ==> "
      << memReg(dstReg) << "[x] == $oldDst[x]);" << endl;
    s << "}" << endl;
  } else {
    s << "procedure $memcpy." << dstReg << "." << srcReg;
    s << "(dest: int, src: int, len: int, align: int, isvolatile: bool);" << endl;
    s << "modifies " << memReg(dstReg) << ";" << endl;
    s << "ensures (forall x:int :: dest <= x && x < dest + len ==> " 
      << memReg(dstReg) << "[x] == old(" << memReg(srcReg) << ")[src - dest + x]);" 
      << endl;
    s << "ensures (forall x:int :: !(dest <= x && x < dest + len) ==> "
      << memReg(dstReg) << "[x] == old(" << memReg(dstReg) << ")[x]);" << endl;
  }

  return s.str();
}

} // namespace smack
