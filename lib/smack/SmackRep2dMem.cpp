#include "SmackRep2dMem.h"

namespace smack {

    const string SmackRep2dMem::PTR_TYPE = "$ptr";
    const string SmackRep2dMem::REF_TYPE = "$ref";

    void SmackRep2dMem::declareGlobals(llvm::Module &m, Program* program) {

      for (llvm::Module::const_global_iterator
          x = m.global_begin(), e = m.global_end(); x != e; ++x) {

          string name = id(x);
          program->addDecl(new ConstDecl(name, REF_TYPE, true));
          program->addDecl(new AxiomDecl(
              Expr::fn(SmackRep::STATIC, Expr::id(name)) ));
      }

      // AXIOMS about variable uniqueness
      // NOTE: This should be covered by the "unique" annotation on the
      // declarations.  What is not covered is that their REFERENCES should
      // be unique...
      // for (unsigned i=0; i<globals.size(); i++)
      //     for (unsigned j=i+1; j<globals.size(); j++)
      //         program->addDecl(new AxiomDecl(
      //             Expr::neq(Expr::id(globals[i]), Expr::id(globals[j])) ));

    }
    
    void SmackRep2dMem::addModifies(Procedure *proc) {
      proc->addMod(MEMORY);
      proc->addMod(ALLOC);
    }

    string SmackRep2dMem::getPtrType() {
      return PTR_TYPE;
    }

    string SmackRep2dMem::getPrelude() {
      return PRELUDE;
    }

    const string SmackRep2dMem::PRELUDE =
        "// SMACK Memory Model\n"
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
        "const unique $NULL: $ref;\n"
        "axiom $static($NULL);\n"
        "const $UNDEF: $ptr;\n"
        "\n"
        "procedure $alloca(obj_size: int) returns (new: $ptr);\n"
        "modifies $Alloc;\n"
        "ensures old($Alloc)[$obj(new)] == $UNALLOCATED && $Alloc[$obj(new)] == $ALLOCATED;\n"
        "ensures !$static($obj(new));\n"
        "ensures $off(new) == 0;\n"
        "ensures $size($obj(new)) == obj_size;\n"
        "ensures (forall x_obj:$ref :: {$Alloc[x_obj]} x_obj == $obj(new) || old($Alloc)[x_obj] == $Alloc[x_obj]);\n"
        "\n"
        "procedure $malloc(obj_size: int) returns (new: $ptr);\n"
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
        "function $pa(pointer: $ptr, offset: int, size: int) returns ($ptr);\n"
        "function $trunc(p: $ptr) returns ($ptr);\n"
        "function $p2i(p: $ptr) returns ($ptr);\n"
        "function $i2p(p: $ptr) returns ($ptr);\n"
        "function $p2b(p: $ptr) returns (bool);\n"
        "function $b2p(b: bool) returns ($ptr);\n"
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
        "axiom (forall p:$ptr, o:int, s:int :: {$pa(p,o,s)} $pa(p,o,s) == $ptr($obj(p), $off(p) + o * s));\n"
        "axiom (forall p:$ptr, o:int, s:int :: {$pa(p,o,s)} $obj($pa(p,o,s)) == $obj(p));\n"
        "axiom (forall p:$ptr :: $trunc(p) == p);\n"
        "\n"
        "axiom $b2i(true) == 1;\n"
        "axiom $b2i(false) == 0;\n"
        "axiom $b2p(true) == $ptr($NULL,1);\n"
        "axiom $b2p(false) == $ptr($NULL,0);\n"
        "\n"
        "axiom (forall i:int :: $i2b(i) <==> i != 0);\n"
        "axiom $i2b(0) == false;\n"
        "axiom (forall r:$ref, i:int :: $p2b($ptr(r,i)) <==> i != 0);\n"
        "axiom $p2b($ptr($NULL,0)) == false;\n"
        "axiom (forall r:$ref, i:int :: $p2i($ptr(r,i)) == $ptr($NULL,i));\n"
        "axiom (forall i:int :: (exists r:$ref :: $i2p($ptr($NULL,i)) == $ptr(r,i)));\n"
        "\n"
        "// SMACK Library Procedures\n"
        "\n"
        "procedure __SMACK_nondet() returns (p: $ptr);\n"
        "procedure __SMACK_nondetInt() returns (p: $ptr);\n"
        "ensures $obj(p) == $NULL;\n"
        "\n"
        "procedure boogie_si_record_int(i: int);\n"
        "procedure boogie_si_record_obj(o: $ref);\n"
        "procedure boogie_si_record_ptr(p: $ptr);\n";

} // namespace smack
