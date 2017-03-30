## FAQ


### On which platforms has SMACK been tested?

Linux, OS X, and Windows/Cygwin. Based on our experience, wherever LLVM can be
built, so can SMACK.


### Which LLVM version is SMACK compatible with?

We note the LLVM release that the current version of SMACK has to be compiled
against in our installation instructions.  It is important to note that since
the LLVM bitcode format is not backward compatible, SMACK is only able to
process bitcode files generated using the specified LLVM release.


### One of SMACK's dependencies fails to build on my system; what should I do?

You should contact the authors of that dependency (e.g., LLVM, Z3, Boogie,
Corral).  While some of these are only supported on certain systems (e.g.,
Boogie/Corral only on Windows), in practice, many, including us, have gotten
them to work on other systems (e.g., Boogie/Corral on Linux & OS X).


## OSX-specific Questions

### Why is `opt -load smack.dylib` failing with an `Undefined symbol` error?

When LLVM is compiled and installed on OSX (with `--enable-optimized`), many
symbols on which `smack.dylib` depends have been stripped from LLVM's `opt`
executable.  Configuring LLVM with `--enable-keep-symbols` resolves this
problem.

