<!-- [![Build Status](http://kornat.cs.utah.edu:8080/job/smack/badge/icon)](http://kornat.cs.utah.edu:8080/job/smack/) -->

# This is a fork of [SMACK](https://github.com/smackers/smack) to verify Rust language programs

## The current goals of this project are:
* An assertion verifier (throught the `assert!` and `assert_eq!` macros) for Rust programs
* Verification of safety properties for *unsafe* blocks, *e.g.*, Rust pointer aliasing rules are not violated, memory is not leaked and null pointers are never exposed
* Detection of out-of-bounds memory accesses
* Context bounded verification of concurrent programs
* Pre and post condition reasoning for FFI functions, *e.g.*, C function calls
* This can be coupled with verification of called C functions for end-to-end verification

## Current requirements
* LLVM 3.6
* [Rust 1.2](http://static.rust-lang.org/dist/2015-06-01/rust-nightly-x86_64-unknown-linux-gnu.tar.gz) *This is the most recent, working vintage Rust compiler for SMACK*
* [Rust 1.2 source](http://static.rust-lang.org/dist/2015-06-01/rustc-nightly-src.tar.gz) *For use with Angelic verification and SDV backtrace viewing*

## Related work
* Rustc and Cargo plugins to ease user experience
* SMACK friendly implementations of common Rust libraries
* Upgrades to SMACK infrastructure to more recent versions of Rust
* Sound implementation of missing LLVM features used by Rust but not Clang

## Contact me for ideas, bugs and other use cases
[Mark S. Baranowski](mailto:baranows@cs.utah.edu)

# Information pertaining to the core SMACK tool

SMACK is a *bounded software verifier*, verifying the assertions in its
input programs up to a given bound on loop iterations and recursion depth.
SMACK can verify C programs, such as the following:

    // examples/simple/simple.c
    #include "smack.h"

    int incr(int x) {
      return x + 1;
    }

    int main(void) {
      int a, b;

      a = b = __VERIFIER_nondet_int();
      a = incr(a);
      assert(a == b + 1);
      return 0;
    }

The command

    smack simple.c

reports that the assertion `a == b + 1` cannot be violated. Besides the
features of this very simple example, SMACK handles every complicated feature
of the C language, including dynamic memory allocation, pointer arithmetic, and
bitwise operations.

Under the hood, SMACK is a translator from the [LLVM](http://www.llvm.org)
compiler’s popular intermediate representation (IR) into the
[Boogie](http://boogie.codeplex.com) intermediate verification language (IVL).
Sourcing LLVM IR exploits an increasing number of compiler front-ends,
optimizations, and analyses. Currently SMACK only supports the C language via
the [Clang](http://clang.llvm.org) compiler, though we are working on providing
support for additional languages. Targeting Boogie exploits a canonical
platform which simplifies the implementation of algorithms for verification,
model checking, and abstract interpretation. Currently, SMACK leverages the
[Boogie](http://boogie.codeplex.com) and [Corral](http://corral.codeplex.com)
verifiers.

This is a class project for CS 6110 at the University of Utah. We are
currently adding missing features to smack to enable the verification of Rust
programs.

Consult [the Wiki](https://github.com/smackers/smack/wiki) for system
requirements, installation, usage, and everything else.

*We are very interested in your experience using SMACK. Please do contact
[Zvonimir](mailto:zvonimir@cs.utah.edu) or
[Michael](mailto:michael.emmi@gmail.com) with any possible feedback.*
