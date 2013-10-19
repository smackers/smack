[SMACK](http://smackers.github.com/smack/) is a modular software verification
infrastructure. The main purpose of SMACK is to lower the bar for experimenting
with software verification and quickly prototyping custom software verifiers.
To achieve that, SMACK relies on the well-known [LLVM](http://www.llvm.org)
compiler infrastructure for its front-end, and
[Boogie](http://boogie.codeplex.com) intermediate verification language for its
back-end. Such separation of concerns and modularity make implementing various
additions and extensions to SMACK relatively easy.  Furthermore, the open
architecture of SMACK encourages prototyping custom software verifiers on top
of SMACK.

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
      __SMACK_assert(a == 2);
      return 0;
    }

To do so, SMACK invokes [Clang](http://clang.llvm.org) to compile `simple.c`
into LLVM bitcode `simple.bc`:

    clang -c -Wall -emit-llvm -O0 -g -I../../include/smack simple.c -o simple.bc

then translates the bitcode `simple.bc` to a program in the
[Boogie](http://boogie.codeplex.com) verification language,

    smackgen.py simple.bc -o simple.bpl

and finally verifies `simple.bpl` with the [Boogie Verifier](http://boogie.codeplex.com)

    Boogie simple.bpl

concluding that the original program `simple.c` is verified to be correct.
While SMACK is designed to be a *modular* verifier, for our convenience, this
whole process has also been wrapped into a single command in SMACK:

    smack-verify.py simple.c -o simple.bpl
    
which equally reports that the program `simple.c` is verified.

## Further Information

For requirements, installation, usage, and whatever else, please consult the
[SMACK Wiki on Github](https://github.com/smackers/smack/wiki).
