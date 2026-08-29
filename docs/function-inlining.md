# SmackFunctionInliner Pass

## Motivation

SMACK uses context-insensitive DSA analysis from sea-dsa. When a function
takes or returns pointers, the context-insensitive analysis merges the
points-to nodes at call sites, losing precision. For example, if `alloc()`
returns a freshly allocated pointer, every caller's returned pointer gets
merged into a single node — even though each call site is independent.

Inlining these functions before DSA runs eliminates the inter-procedural
pointer flow, allowing DSA to treat each (formerly separate) call site's
allocations and pointer operations locally. This improves precision without
requiring a context-sensitive analysis.

## Design

`SmackFunctionInliner` is an LLVM `ModulePass` that runs in the `llvm2bpl`
pipeline **before** sea-dsa analysis. It uses LLVM's `InlineFunction` utility
to inline small functions, with a higher threshold for functions that involve
pointers.

### Inlining criteria

A function is eligible for inlining if **all** of the following hold:

- It has a definition (not a declaration or intrinsic)
- It is not variadic
- Its name does not contain `__SMACK_` or `__VERIFIER_`
- It is not an entry point (as specified by `--entry-points`)
- It is not recursive (see below)
- Its instruction count is within the threshold:
  - **Pointer-involving** (returns or takes a pointer): <= `--ptr-inline-limit` (default 200)
  - **Non-pointer**: <= `--inline-limit` (default 50)

The `noinline` attribute (which clang adds to all functions at `-O0`) is
stripped before inlining, since this pass inlines for analysis precision,
not as a compiler optimization.

### Recursion detection

The pass builds an LLVM `CallGraph` and uses `scc_iterator` to identify
strongly connected components (SCCs):

- **Non-trivial SCC** (size > 1): all functions in the SCC are mutually
  recursive and excluded from inlining.
- **Trivial SCC** (size 1): the function is checked for a self-call edge.
  If present, it is directly recursive and excluded.

This prevents infinite inlining of recursive call chains.

### Bottom-up processing

`scc_iterator` yields SCCs in reverse topological order — callees before
callers. The pass processes functions in this order so that when a caller
is inlined, its callees have already been inlined into it. For a chain
`main → foo → bar`, the pass first inlines `bar` into `foo`, then inlines
`foo` (now containing `bar`'s body) into `main`.

### Iterative fixpoint

The pass repeats until no more inlining occurs. This handles cases where
inlining changes the call graph (e.g., a function that was above the
threshold shrinks after dead code is removed, or inlining removes the last
caller of a function which is then deleted, changing reachability).

After each iteration, functions with no remaining callers are removed
(excluding entry points and `__SMACK_`/`__VERIFIER_` functions).

## Command-line options

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `--inline-funcs` | bool | true | Enable/disable the pass |
| `--inline-limit` | unsigned | 50 | Instruction count threshold for non-pointer functions (0 disables) |
| `--ptr-inline-limit` | unsigned | 200 | Instruction count threshold for pointer-involving functions |

## Pipeline placement

The pass is inserted in `llvm2bpl.cpp` after dead code elimination and
`RemoveDeadDefs`, but before `seadsa::createRemovePtrToIntPass()` and all
subsequent DSA-dependent passes:

```
... createDeadCodeEliminationPass()
... RemoveDeadDefs()
>>> SmackFunctionInliner()       ← here
... createRemovePtrToIntPass()
... createLowerSwitchPass()
... createPromoteMemoryToRegisterPass()
...
```

## Files

- `include/smack/SmackFunctionInliner.h` — Pass declaration
- `lib/smack/SmackFunctionInliner.cpp` — Pass implementation
- `tools/llvm2bpl/llvm2bpl.cpp` — Pipeline integration
- `CMakeLists.txt` — Build integration
