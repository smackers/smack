#include "SmackRepFlatMem.h"

namespace smack {

const string SmackRepFlatMem::CURRADDR = "$CurrAddr";
const string SmackRepFlatMem::PTR_TYPE = "int";

vector<const Decl*> SmackRepFlatMem::globalDecl(const llvm::Value* g) {
  vector<const Decl*> decls;
  string name = id(g);
  decls.push_back(Decl::constant(name, getPtrType(), true));

  // TODO fix this
  int size = 1024;

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
  mods.push_back(MEMORY);
  mods.push_back(ALLOC);
  mods.push_back(CURRADDR);
  return mods;
}

string SmackRepFlatMem::getPtrType() {
  return PTR_TYPE;
}

string SmackRepFlatMem::getPrelude() {
  return PRELUDE + SmackRep::getPrelude();
}

const string SmackRepFlatMem::PRELUDE =
  "// SMACK Flat Memory Model\n"
  "\n"
  "function $ptr(obj:int, off:int) returns (int) {obj + off}\n"
  "function $size(int) returns (int);\n"
  "function $obj(int) returns (int);\n"
  "function $off(ptr:int) returns (int) {ptr}\n"
  "\n"
  "var $Mem: [int] int;\n"
  "var $Alloc: [int] bool;\n"
  "var $CurrAddr:int;\n"
  "\n"
  "const unique $NULL: int;\n"
  "axiom $NULL == 0;\n"
  "const $UNDEF: int;\n"
  "\n"
  "procedure $malloc(obj_size: int) returns (new: int);\n"
  "modifies $CurrAddr, $Alloc;\n"
  "requires obj_size > 0;\n"
  "ensures 0 < old($CurrAddr);\n"
  "ensures new == old($CurrAddr);\n"
  "ensures $CurrAddr > old($CurrAddr) + obj_size;\n"
  "ensures $size(new) == obj_size;\n"
  "ensures (forall x:int :: new <= x && x < new + obj_size ==> $obj(x) == new);\n"
  "ensures $Alloc[new];\n"
  "ensures (forall x:int :: {$Alloc[x]} x == new || old($Alloc)[x] == $Alloc[x]);\n"
  "\n"
  "procedure $alloca(obj_size: int) returns (new: int);\n"
  "modifies $CurrAddr, $Alloc;\n"
  "requires obj_size > 0;\n"
  "ensures 0 < old($CurrAddr);\n"
  "ensures new == old($CurrAddr);\n"
  "ensures $CurrAddr > old($CurrAddr) + obj_size;\n"
  "ensures $size(new) == obj_size;\n"
  "ensures (forall x:int :: new <= x && x < new + obj_size ==> $obj(x) == new);\n"
  "ensures $Alloc[new];\n"
  "ensures (forall x:int :: {$Alloc[x]} x == new || old($Alloc)[x] == $Alloc[x]);\n"
  "\n"
  "procedure $free(pointer: int);\n"
  "modifies $Alloc;\n"
  "requires $Alloc[pointer];\n"
  "requires $obj(pointer) == pointer;\n"
  "ensures !$Alloc[pointer];\n"
  "ensures (forall x:int :: {$Alloc[x]} x == pointer || old($Alloc)[x] == $Alloc[x]);\n"
  "\n"
  "procedure $memcpy(dest:int, src:int, len:int, align:int, isvolatile:bool);\n"
  "modifies $Mem;\n"
  "ensures (forall x:int :: dest <= x && x < dest + len ==> $Mem[x] == old($Mem)[src - dest + x]);\n"
  "ensures (forall x:int :: !(dest <= x && x < dest + len) ==> $Mem[x] == old($Mem)[x]);\n"
  "\n"
  "function $pa(pointer: int, offset: int, size: int) returns (int);\n"
  "function $trunc(p: int) returns (int);\n"
  "function $p2i(p: int) returns (int);\n"
  "function $i2p(p: int) returns (int);\n"
  "function $p2b(p: int) returns (bool);\n"
  "function $b2p(b: bool) returns (int);\n"
  "\n"
  "axiom (forall p:int, o:int, s:int :: {$pa(p,o,s)} $pa(p,o,s) == p + o * s);\n"
  "axiom (forall p:int :: $trunc(p) == p);\n"
  "\n"
  "axiom $b2p(true) == 1;\n"
  "axiom $b2p(false) == 0;\n"
  "axiom (forall i:int :: $p2b(i) <==> i != 0);\n"
  "axiom $p2b(0) == false;\n"
  "axiom (forall i:int :: $p2i(i) == i);\n"
  "axiom (forall i:int :: $i2p(i) == i);\n"
  "\n"
  "procedure __SMACK_nondet() returns (p: int);\n"
  "procedure __SMACK_nondetInt() returns (p: int);\n";

} // namespace smack
