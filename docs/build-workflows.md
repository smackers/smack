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
smack main.c helper.c -t -bpl main.bpl
```

This is useful when debugging translation issues or when passing Boogie to a
separate verifier invocation.

### Prelinked LLVM Bitcode

For larger builds, generate one whole-program bitcode file yourself and pass it
to SMACK:

```Shell
clang -c -emit-llvm -O0 -g -Xclang -disable-O0-optnone \
  -I/path/to/smack/share/smack/include main.c -o main.bc
clang -c -emit-llvm -O0 -g -Xclang -disable-O0-optnone \
  -I/path/to/smack/share/smack/include helper.c -o helper.bc
llvm-link main.bc helper.bc -o program.bc
smack program.bc
```

Use the same preprocessor defines and include paths that you would use for a
normal build. SMACK adds its own runtime model during verification, so do not
manually link `share/smack/lib/*.c` unless you are deliberately experimenting
with the internals.

### Makefile-Style Build

A project build can produce bitcode by setting the compiler and linker to LLVM
tools. The `examples/simple-project/Makefile` uses this pattern:

```Makefile
CC = clang
LD = llvm-link
INC = /path/to/smack/share/smack/include
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = incr.c simple.c
OBJS = $(subst .c,.bc,$(SOURCES))

all: $(OBJS)
	$(LD) -o simple-project.bc $(OBJS)
```

After building the bitcode:

```Shell
smack simple-project.bc
```

This replaces older documentation that recommended whole-program-llvm as the
default route. Whole-program-llvm can still be useful in some environments, but
SMACK does not require it. Prefer direct multi-file invocation or an explicit
Clang/`llvm-link` bitcode build when writing reproducible documentation and
tests.

### Existing Build Systems

For a build system you do not want to rewrite, the usual approach is:

1. Identify the compile commands for the translation units you want to verify.
2. Replace native object generation with `clang -c -emit-llvm`.
3. Preserve include paths, target flags, and relevant `-D` definitions.
4. Use `-O0 -g -Xclang -disable-O0-optnone` unless there is a specific reason
   to verify optimized IR.
5. Link the resulting `.bc` files with `llvm-link`.
6. Run SMACK on the linked `.bc` file.

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
- If assertions appear to be ignored in C/C++, include `<assert.h>` or
  `<cassert>`.
