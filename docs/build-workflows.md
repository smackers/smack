## Build Workflows

SMACK verifies the LLVM module produced from the files you pass on the command
line. For a single C file this is hidden behind `smack file.c`; for larger
programs it helps to understand where the compilation and linking steps happen.

### Single Source File

For one C file, pass it directly to SMACK:

```Shell
smack main.c
```

SMACK invokes Clang with debug information enabled, links in the relevant SMACK
runtime model, translates the resulting LLVM bitcode to Boogie, and invokes the
selected verifier.

Use `--clang-options` for ordinary compiler flags:

```Shell
smack main.c --clang-options="-Iinclude -DVERIFYING"
```

### Multiple Source Files

Pass every translation unit needed for the verification target:

```Shell
smack main.c account.c ledger.c
```

SMACK compiles each source file to LLVM bitcode and links the bitcode modules
before verification. This is the preferred workflow for small projects and for
regressions.

The `examples/simple-project` directory shows this pattern with two C files,
`simple.c` and `incr.c`.

### Saving Intermediate Artifacts

Use these options when you need to inspect or reuse intermediate files:

```Shell
smack main.c helper.c -bc main.bc -ll main.ll -bpl main.bpl
```

- `-bc` saves the initial LLVM bitcode.
- `-ll` saves the LLVM IR after SMACK's LLVM passes.
- `-bpl` saves the generated Boogie program.
- `-t` translates only and skips verification.

For example:

```Shell
smack main.c helper.c -t -bc program.bc -bpl main.bpl \
  --check assertions integer-overflow
```

This is useful when debugging translation issues or when passing Boogie to a
separate verifier invocation. Options that affect source compilation must be
selected when the bitcode is created. In particular,
`--check integer-overflow` makes SMACK ask Clang to instrument signed overflow
and shifts. If the saved bitcode is verified later, use the same property
selection:

```Shell
smack program.bc --check assertions integer-overflow
```

### Prelinked LLVM Bitcode

For larger builds, the safest way to generate one whole-program bitcode file is
to let SMACK compile and link the sources with the intended property options:

```Shell
smack main.c helper.c -t -bc program.bc \
  --check assertions integer-overflow
smack program.bc --check assertions integer-overflow
```

This preserves the property-specific source instrumentation used by SMACK's
front end. Passing prebuilt bitcode to SMACK is too late to add instrumentation
that Clang must insert while compiling the source.

If the build must invoke LLVM tools directly, use the LLVM major version that
SMACK was built for. This checkout currently uses LLVM 14, so the equivalent
commands for checking assertions and integer overflow are:

```Shell
clang-14 -c -emit-llvm -O0 -g -Xclang -disable-O0-optnone \
  -fsanitize=signed-integer-overflow,shift \
  -I/path/to/smack/share/smack/include main.c -o main.bc
clang-14 -c -emit-llvm -O0 -g -Xclang -disable-O0-optnone \
  -fsanitize=signed-integer-overflow,shift \
  -I/path/to/smack/share/smack/include helper.c -o helper.bc
llvm-link-14 main.bc helper.bc -o program.bc
smack program.bc --check assertions integer-overflow
```

Use the same preprocessor defines and include paths that you would use for a
normal build. Reproduce every source-level flag required by the selected SMACK
configuration; the sanitizer flag above is required for integer-overflow
checking. Other properties or encodings can require different defines or
compiler options, which is why using `smack -t -bc` is preferred. SMACK adds
its own runtime model during verification, so do not manually link
`share/smack/lib/*.c` unless you are deliberately experimenting with the
internals.

### Makefile-Style Build

A project build can produce bitcode by setting the compiler and linker to LLVM
tools. The `examples/simple-project/Makefile` uses this pattern:

```Makefile
CC = clang-14
LD = llvm-link-14
INC = /path/to/smack/share/smack/include
CFLAGS = -c -Wall -emit-llvm -O0 -g -Xclang -disable-O0-optnone \
         -fsanitize=signed-integer-overflow,shift -I$(INC)

SOURCES = incr.c simple.c
OBJS = $(subst .c,.bc,$(SOURCES))

all: $(OBJS)
	$(LD) -o simple-project.bc $(OBJS)
```

After building the bitcode:

```Shell
smack simple-project.bc --check assertions integer-overflow
```

This Makefile intentionally prepares bitcode for integer-overflow checking. If
the project checks a different property set, adjust both `CFLAGS` and the
matching SMACK command. Also update the `-14` suffixes together when using a
SMACK installation built against a different LLVM major version.

This replaces older documentation that recommended whole-program-llvm as the
default route. Whole-program-llvm can still be useful in some environments, but
SMACK does not require it. Prefer direct multi-file invocation or an explicit
Clang/`llvm-link` bitcode build when writing reproducible documentation and
tests.

### Existing Build Systems

For a build system you do not want to rewrite, the usual approach is:

1. Identify the compile commands for the translation units you want to verify.
2. Replace native object generation with the version-matched compiler, currently
   `clang-14 -c -emit-llvm`.
3. Preserve include paths, target flags, and relevant `-D` definitions.
4. Use `-O0 -g -Xclang -disable-O0-optnone` unless there is a specific reason
   to verify optimized IR.
5. Reproduce property-specific compilation flags. In particular, add
   `-fsanitize=signed-integer-overflow,shift` to every C/C++ compilation when
   checking `integer-overflow`.
6. Link the resulting `.bc` files with the version-matched linker, currently
   `llvm-link-14`.
7. Run SMACK on the linked `.bc` file with the same property selection used to
   prepare the sources.

SMACK also has a JSON compilation database front-end, but it is less commonly
used than direct source or bitcode input. Treat it as an advanced workflow and
check the generated `.bc`/`.bpl` artifacts when using it.

### Entry Points

By default, SMACK verifies `main`. Use `--entry-points` when the verification
target is another function:

```Shell
smack library.c --entry-points verify_account
```

Multiple entry points are allowed:

```Shell
smack library.c --entry-points verify_deposit verify_withdraw
```

### Common Build Problems

- If Clang cannot find `smack.h`, add the installed SMACK include directory with
  `--clang-options="-I/path/to/smack/share/smack/include"` or add it to the
  manual bitcode compile command.
- If the verifier reports unresolved functions, make sure every needed source
  file or bitcode module was included in the link.
- If debug traces do not point to useful source locations, compile with `-g`.
- If optimized IR hides the source shape you expected, start with `-O0` and
  only move to optimized IR after the property is understood.
- If integer-overflow checking finds nothing in manually compiled bitcode,
  confirm that every source file was compiled with
  `-fsanitize=signed-integer-overflow,shift` before linking.
- If LLVM rejects or misreads a bitcode file, confirm that Clang, `llvm-link`,
  and SMACK use the same LLVM major version.
- If assertions appear to be ignored in C/C++, include `<assert.h>` or
  `<cassert>`.
