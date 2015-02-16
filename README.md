At its core, SMACK is a translator from the [LLVM](http://www.llvm.org)
compiler's popular intermediate representation (IR) into the
[Boogie](http://boogie.codeplex.com) intermediate verification language (IVL).
Sourcing LLVM IR exploits an increasing number of compiler frontends,
optimizations, and analyses. Targeting Boogie exploits a canonical platform
which simplifies the implementation of algorithms for verification, model
checking, and abstract interpretation. The main purpose of SMACK is to decouple
the implementations of verification algorithms from the details of source
languages, and enable rapid prototyping on production code.  Our initial
experience verifying C language programs is encouraging: SMACK is competitive
in SV-COMP benchmarks, is able to translate large programs (100 KLOC), and is
used in several verification research prototypes.

*Please drop us a note if using SMACK in your research or teaching. We would
love to learn more about your experience.*

## A Quick Demo

SMACK can verify C programs, such as the following:

    // simple.c
    #include "smack.h"

    int incr(int x) {
      return x + 1;
    }

    int main(void) {
      int a;

      a = 1;
      a = incr(a);
      assert(a == 2);
      return 0;
    }

To do so, SMACK invokes [Clang](http://clang.llvm.org) to compile `simple.c`
into LLVM bitcode `simple.bc`:

    clang -c -Wall -emit-llvm -O0 -g -I../../include/smack simple.c -o simple.bc

then translates the bitcode `simple.bc` to a program in the
[Boogie](http://boogie.codeplex.com) verification language,

    smackgen.py simple.bc -o simple.bpl

and finally verifies `simple.bpl` with the [Boogie](http://boogie.codeplex.com)
or [Corral/Duality](http://corral.codeplex.com) verifiers

    boogie simple.bpl

concluding that the original program `simple.c` is verified to be correct.
While SMACK is designed to be a *modular* verifier, for our convenience, this
whole process has also been wrapped into a single command in SMACK:

    smackverify.py simple.c -o simple.bpl
    
which equally reports that the program `simple.c` is verified.

## Further Information

For requirements, installation, usage, and whatever else, please consult the
[SMACK Wiki on Github](https://github.com/smackers/smack/wiki).
