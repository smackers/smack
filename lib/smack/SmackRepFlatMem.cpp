#include "SmackRepFlatMem.h"

namespace smack {

    const string SmackRepFlatMem::CURRADDR = "$CurrAddr";
    const string SmackRepFlatMem::PTR_TYPE = "int";

    void SmackRepFlatMem::declareGlobals(llvm::Module &m, Program* program) {
      vector<string> globals;
      for (llvm::Module::const_global_iterator
          x = m.global_begin(), e = m.global_end(); x != e; ++x) {

          string name = id(x);
          globals.push_back(name);
          program->addDecl(new ConstDecl(name, getPtrType(), true));
      }

      // TODO: size of globals is currently hard-coded to 1024
      if (!globals.empty()) {
          for (unsigned i=0; i<globals.size()-1; i++)
              program->addDecl(new AxiomDecl(
                  Expr::fn("$slt", Expr::fn(SmackRep::ADD, Expr::id(globals[i]), Expr::lit(1024)),
                  Expr::id(globals[i+1]))));
          program->addDecl(new AxiomDecl(
              Expr::fn("$slt", Expr::fn(SmackRep::ADD, Expr::id(globals[globals.size()-1]), Expr::lit(1024)),
              Expr::lit(0))));
      }
    }

    void SmackRepFlatMem::declareFunctionPointer(string name, Program* program) {
      program->addDecl(new ConstDecl(name, getPtrType(), true));
    }
    
    void SmackRepFlatMem::addModifies(Procedure *proc) {
      proc->addMod(MEMORY);
      proc->addMod(ALLOC);
      proc->addMod(CURRADDR);
    }

    string SmackRepFlatMem::getPtrType() {
      return PTR_TYPE;
    }

    string SmackRepFlatMem::getPrelude() {
      return PRELUDE;
    }

    const string SmackRepFlatMem::PRELUDE =
        "// SMACK Memory Model\n"
        "\n"
        "function $ptr(obj:int, off:int) returns (int) {obj + off}\n"
        "function $off(ptr:int) returns (int) {ptr}\n"
        "\n"
        "const unique $NULL: int;\n"
        "axiom $NULL == 0;\n"
        "const $UNDEF: int;\n"
        "\n"
        "// function $size(int) returns (int);\n"
        "// type $name;\n"
        "// const unique $UNALLOCATED: $name;\n"
        "// const unique $ALLOCATED: $name;\n"
        "var $Mem: [int] int;\n"
        "var $CurrAddr:int;\n"
        "var $Alloc: [int] bool;\n"
        "\n"
        "procedure $malloc(obj_size: int) returns (new: int);\n"
        "modifies $CurrAddr, $Alloc;\n"
        "requires obj_size > 0;\n"
        "ensures 0 < old($CurrAddr);\n"
        "ensures new == old($CurrAddr);\n"
        "ensures $CurrAddr > old($CurrAddr) + obj_size;\n"
        "ensures $Alloc[new];\n"
        "ensures (forall x:int :: {$Alloc[x]} x == new || old($Alloc)[x] == $Alloc[x]);\n"
        "\n"
        "procedure $alloca(obj_size: int) returns (new: int);\n"
        "modifies $CurrAddr, $Alloc;\n"
        "requires obj_size > 0;\n"
        "ensures 0 < old($CurrAddr);\n"
        "ensures new == old($CurrAddr);\n"
        "ensures $CurrAddr > old($CurrAddr) + obj_size;\n"
        "ensures $Alloc[new];\n"
        "ensures (forall x:int :: {$Alloc[x]} x == new || old($Alloc)[x] == $Alloc[x]);\n"
        "\n"
        "procedure $free(pointer: int);\n"
        "modifies $Alloc;\n"
        "requires $Alloc[pointer];\n"
        "ensures !$Alloc[pointer];\n"
        "ensures (forall x:int :: {$Alloc[x]} x == pointer || old($Alloc)[x] == $Alloc[x]);\n"
        "\n"
        "// SMACK Arithmetic Predicates\n"
        "\n"
        "function $add(p1:int, p2:int) returns (int) {p1 + p2}\n"
        "function $sub(p1:int, p2:int) returns (int) {p1 - p2}\n"
        "function $mul(p1:int, p2:int) returns (int) {p1 * p2}\n"
        "function $sdiv(p1:int, p2:int) returns (int);\n"
        "function $udiv(p1:int, p2:int) returns (int);\n"
        "function $srem(p1:int, p2:int) returns (int);\n"
        "function $urem(p1:int, p2:int) returns (int);\n"
        "function $and(p1:int, p2:int) returns (int);\n"
        "function $or(p1:int, p2:int) returns (int);\n"
        "function $xor(p1:int, p2:int) returns (int);\n"
        "function $lshr(p1:int, p2:int) returns (int);\n"
        "function $ashr(p1:int, p2:int) returns (int);\n"
        "function $shl(p1:int, p2:int) returns (int);\n"
        "function $ult(p1:int, p2:int) returns (bool) {p1 < p2}\n"
        "function $ugt(p1:int, p2:int) returns (bool) {p1 > p2}\n"
        "function $ule(p1:int, p2:int) returns (bool) {p1 <= p2}\n"
        "function $uge(p1:int, p2:int) returns (bool) {p1 >= p2}\n"
        "function $slt(p1:int, p2:int) returns (bool) {p1 < p2}\n"
        "function $sgt(p1:int, p2:int) returns (bool) {p1 > p2}\n"
        "function $sle(p1:int, p2:int) returns (bool) {p1 <= p2}\n"
        "function $sge(p1:int, p2:int) returns (bool) {p1 >= p2}\n"
        "\n"
        "function $pa(pointer: int, offset: int, size: int) returns (int);\n"
        "function $trunc(p: int) returns (int);\n"
        "function $p2i(p: int) returns (int);\n"
        "function $i2p(p: int) returns (int);\n"
        "function $p2b(p: int) returns (bool);\n"
        "function $b2p(b: bool) returns (int);\n"
        "function $i2b(i: int) returns (bool);\n"
        "function $b2i(b: bool) returns (int);\n"
        "\n"
        "// SMACK Arithmetic Axioms\n"
        "\n"
        "axiom $and(0,0) == 0;\n"
        "axiom $and(0,1) == 0;\n"
        "axiom $and(1,0) == 0;\n"
        "axiom $and(1,1) == 1;\n"
        "\n"
        "axiom $or(0,0) == 0;\n"
        "axiom $or(0,1) == 1;\n"
        "axiom $or(1,0) == 1;\n"
        "axiom $or(1,1) == 1;\n"
        "\n"
        "axiom $xor(0,0) == 0;\n"
        "axiom $xor(0,1) == 1;\n"
        "axiom $xor(1,0) == 1;\n"
        "axiom $xor(1,1) == 0;\n"
        "\n"
        "axiom (forall p:int, o:int, s:int :: {$pa(p,o,s)} $pa(p,o,s) == p + o * s);\n"
        "axiom (forall p:int :: $trunc(p) == p);\n"
        "\n"
        "axiom $b2i(true) == 1;\n"
        "axiom $b2i(false) == 0;\n"
        "axiom $b2p(true) == 1;\n"
        "axiom $b2p(false) == 0;\n"
        "\n"
        "axiom (forall i:int :: $i2b(i) <==> i != 0);\n"
        "axiom $i2b(0) == false;\n"
        "axiom (forall i:int :: $p2b(i) <==> i != 0);\n"
        "axiom $p2b(0) == false;\n"
        "axiom (forall i:int :: $p2i(i) == i);\n"
        "axiom (forall i:int :: $i2p(i) == i);\n"
        "\n"
        "// SMACK Library Procedures\n"
        "\n"
        "procedure __SMACK_nondet() returns (p: int);\n"
        "procedure __SMACK_nondetInt() returns (p: int);\n"
        "\n"
        "// procedure boogie_si_record_int(i: int);\n"
        "// procedure boogie_si_record_obj(o: $ref);\n"
        "// procedure boogie_si_record_ptr(p: $ptr);\n";

} // namespace smack
