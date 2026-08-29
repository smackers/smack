
# Using SMACK with your favorite programming language.

In theory, SMACK can be used to verify any langauge that compiles to LLVM IR. 
In practice, due to language-specific peculiarities, it is not always clear how
well SMACK will work on any given language. However, our experience has been
positive, especially with C-family languages.

Currently, we have rudimentary SMACK bindings for the following languages:
C, C++, Rust, D, FORTRAN, and Objective-C. This document is for users of other
languages, or users who need more than what SMACK provides in one of the listed
examples. 

### Prerequisites

- An Ahead of Time compiler that targets the same version of LLVM as SMACK.
 
For compatibility, SMACK version == LLVM version - 2. So, for LLVM 3.9, 
you want SMACK 1.9, etc.

- A way of importing C headers and calling C functions from your language

### Tutorial

Step 1: Import smack.h using the C-import functionality

You can use the functions smack.h to call verifier operations like 
`__VERIFIER_assert`. Note that functions in smack.h follow the C style
of using integers as booleans, so it may be good to write a wrapper that
takes advantage of your language's first-class boolean type.

Step 2: Compile to LLVM IR

Compile your code to either a .ll or a .bc file (the two formats are equivalent). 
Most compilers provide a command-line option like `-emit-llvm` or `-output-ll`. 
You should also add debug symbols, which is `-g` on most compilers. 
Disabling optimizations may also be useful, with `-O0` or similar.

Step 3: Find the entry point

Inspect the code to find the `main` function or equivalent entry point. Add 
`--entry-points [mainfunction]` whenever you call SMACK if this is anything 
other than `main`.

If you chose to compile your program into a .bc, you can use llvm-dis and 
llvm-as to convert between bitcode and human-readable format.

Step 4: Run SMACK!

Now, you can run SMACK on your .ll or .bc file. There may be small bugs if your 
compiler uses LLVM features that aren't used by current languages. If there 
are any problems, feel free to open an issue. 

### Example commands

#### Clang

`clang -S -g -O0 -emit-llvm program.c`

Note: as flang implements the same compiler options as clang, we can compile 
FORTRAN for SMACK with  

`flang -S -g -O0 -emit-llvm program.f90`

#### Swift

`swiftc -g -emit-ir -import-objc-header smack.h program.swift > program.ll`

#### D

`ldc2 -g -O0 -output-ll program.d`
