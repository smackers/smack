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


## Requirements

### Dependencies

SMACK depends on the following projects:
* [LLVM](http://www.llvm.org) (release [3.2](http://llvm.org/releases/download.html#3.2)),
  [clang](http://clang.llvm.org) (release [3.2](http://llvm.org/releases/download.html#3.2))
* [Python](http://www.python.org) (version 2.7)

Currently, SMACK supports the following back-end verifiers:
* [Boogie](http://boogie.codeplex.com), default theorem prover is [Z3](http://z3.codeplex.com/)
* [Corral](http://corral.codeplex.com), default theorem prover is [Z3](http://z3.codeplex.com/)

To configure, build, and install LLVM and clang, follow their [Getting Started
Quickly](http://llvm.org/docs/GettingStarted.html#getting-started-quickly-a-summary)
summary. You have to build and install LLVM and clang from sources since SMACK
does not build properly with their packaged versions. SMACK supports only major
LLVM releases and not the latest version found on its Subversion repository.
Therefore, instead of checking out LLVM from SVN, download its sources for the
required release as noted above.

### Supported Platforms

SMACK is known to work on the following platforms:
* Linux (Ubuntu)
* MacOS
* Cygwin

**Note for Cygwin users:**
You should configure LLVM/clang with the --enable-shared option (which may also
require the --enable-optimized option).  Then when configuring SMACK you should
use these options as well.


## Getting Started Quickly (on Linux)

To get you started with SMACK quickly, we provide a reference installation
script that downloads and installs Z3, Boogie, LLVM/clang, and SMACK. Simply
download
[build-linux.sh](http://github.com/smackers/smack/blob/master/bin/build-linux.sh)
and execute it.

Note that this script is primarily provided as a reference and we do not expect
it will work out-of-the-box on all platforms and required software
combinations. You can still give it a try and modify it based on your specific
needs.

**Known problems:**
Z3 source code cannot be cloned from codeplex using git sometimes. This is a
known
[problem](http://z3.codeplex.com/wikipage?title=Git%20HTTPS%20cloning%20errors).
In that case you can manually download Z3's sources from its codeplex site.


## Getting Started with SMACK

### Installation Guide

1. Checkout SMACK:

   ```
   cd where-you-want-smack-source-to-live  
   git clone git@github.com:smackers/smack.git
   ```

2. Configure SMACK:

   ```
   cd where-you-want-to-build-smack
   mkdir build (for building without polluting the source dir)
   cd build
   ../smack/configure --with-llvmsrc=<directory> --with-llvmobj=<directory> --prefix=<directory>
   ```

   Options for configure are:
   * --with-llvmsrc=<directory>  : Tell SMACK where the LLVM source tree is located [required].
   * --with-llvmobj=<directory>  : Tell SMACK where the LLVM object tree is located [required].
   * --prefix=<directory>        : Specify full pathname of where you want SMACK installed [required].
   * --enable-optimized          : Compile with optimizations enabled [default is NO].
   * --enable-assertions         : Compile with assertion checks enabled [default is YES].

3. Build and install SMACK:

   ```
   make
   make install
   ```

   If everything goes well, you should now have lib/libsmack.a and lib/smack.so
   (or smack.dylib on MacOS, or smack.dll on Cygwin) in the SMACK installation
   directory.

4. Create an environment variable called BOOGIE containing a Boogie invocation
   command for your platform. For example:

   ```
   export BOOGIE="mono /home/john/Boogie/Binaries/Boogie.exe"
   ```

   Similarly, if using Corral create an environment variable called CORRAL.

**Important note:**
LLVM/clang binaries (e.g., clang, llvm-link, opt) should all be in your path,
as well as your smack-install-dir/bin directory!


### Running Regression Tests

To make sure SMACK has been installed properly, run its regression tests.  Go
to smack/test directory and compile the regression tests by running `make`. You
should get a number of LLVM bitcode files, one per test.  Execute the
regression test script with `./regtest.py` (or `./regtest-corral.py` if using
Corral). All tests should pass.


## SMACK Tools

Currently, SMACK comes with the following tools in the bin directory:
* llvm2bpl is a bare-bone translator from LLVM bitcode into plain Boogie.
* smackgen generates output Boogie files specifically formatted for a chosen
  back-end verifier.
* smack-verify is a tool for statically verifying properties of programs written in
  C/C++. For a given input program, the tool checks for violations of
  user-provided assertions.

Type `llvm2bpl.py -h`, `smackgen.py -h`, or `smack-verify.py -h` for a full
list of supported command line options.


## The SMACK Verifier User Guide

Next, we illustrate how to verify the following simple C program using the SMACK
verifier:
```
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
```
Note that this example can also be found in the smack/examples/simple
directory.

Simply run the SMACK verifier on your input C file:
```
smack-verify.py simple.c -o simple.bpl
```
SMACK should report no errors for this example.

Under the hood, SMACK first compiles the example into an LLVM bitcode file using clang:
```
clang -c -Wall -emit-llvm -O0 -g -I../../include/smack simple.c -o simple.bc
```
We use the -g flag to compile with debug information enabled, which the SMACK
verifier leverages to generate more informative error traces. Then, the generated bitcode
file is translated into Boogie code, which is in turn passed to the chosen back-end
verifier.
