# Introduction
SMACK has rudimentary support for Rust programs. Development is active to improve SMACK's support and scalability. For general usage, consult [usage](usage-notes.md).

# SMACK verification functions
To include all SMACK verification features, use:
```rust
#[macro_use]
extern crate smack;
use smack::*;
```

Two macros are provided:
- `smack::assert!` for checking assertions in the program
- `smack::assume!` for making verification assumptions

In addition the `smack` crate provides the `VerifierNonDet` trait and automatically implements it for the primitive types.
This can be done by, for example, `let x = 4u32.verifier_nondet()` this works because the `VerifierNonDet` trait is implemented for the `u32` type.

To implement `VerifierNondet` for a structure, simply implement the trait for the structure using the implementations of its members.

# Rust features supported
The following work as expected in SMACK:
- Generics
- Trait polymorphism
- Slices
- Closures
- Floating points
- Etc.

# Rust specific features
- The `--checks=rust-panics` option can be used to check for panics in a Rust program.
By default panics are ignored by SMACK.
Notice that this can detect some memory safety issues such as buffer overflow

- 
# Models provided
## Vector
A basic vector container is provided, as `smack::Vec` along with the `vec!` macro exported by the `smack` crate providing some compatability with existing codes.
This implementation does not support more advanced vector operations, but should support most uses of the vector container.
## Box
This is provided for compatibility.
The implementation is incomplete, however SMACK is now capable of handling the standard library's `Box` class, so that is the recommended implementation to use.
## Memory allocation functions
The `GlobalAlloc` and `Allocator` traits are supported for implementing structs.
However, these will ultimately call SMACK's memory management functions.

# Spurius models and tips
- Due to SMACK's use of imprecise DSA to split memory regions, there are some patterns used by the Rust compiler that incorrectly lead to aliasing memory regions being treated as non-aliasing.
To alleviate this, SMACK can be used with the `--no-memory-splitting` option, however this may significantly increase verification times.
- SMACK's default backend verifier is Corral. We have found that for Rust programs the Boogie verifier is often significantly faster. This can be enabled with `--verifier=boogie`.