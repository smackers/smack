# Motivation
For verification purposes, it is often best to provide verifier friendly models to substitute for the implementations found in the standard library.
However, there are situations where it may be desirable to use a modified standard implementation.
In Smack, this is to have custom implementations used throughout an entire crate, and to improve trust in the models.

# Including the Standard Library
The Cargo argument `-Zbuild-std` causes Cargo to build and link the Rust standard library from source.
This allows Smack to use a customized version of the standard library that is more amenable to verification.
The `__CARGO_TESTS_ONLY_SRC_ROOT` environmental variable tells Cargo where to find the source code root to use.
The source for the standard library can be obtained using the command `rustup component add rust-src --toolchain $VERSION`.
The source can also be obtained from https://github.com/rust-lang/rust.
This method requires running part of the Rust compiler build script in order to download some necessary packages used by the standard library.

# Example modification
In Smack it is desirable to allocate memory upfront in order to avoid a `realloc` later.
For the `Vec` struct we can modify the `new` function in `library/alloc/src/raw_vec.rs` to use a static, non-zero sized allocation.
Specifically, we change this:
```rust
pub const fn new() -> Self {
    Self::new_in(Global)
}
```
to this:
```rust
#[cfg(verifier = "smack")]
pub fn new() -> Self {
    Self::with_capacity_in(32, Global)
}

#[cfg(not(verifier = "smack"))]
pub const fn new() -> Self {
    Self::new_in(Global)
}
```

Here, we use conditional compilation on the verifier configuration to control which version of the code is compiled.
While this may seem redundant, this serves two purposes: the first is that we only added code, making future merges easier.
Secondly, this documents which functions were changed for Smack, making customizations easier to locate in the source code.