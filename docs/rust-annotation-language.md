The syntax for these annotations is inspired by the rust-verification-language project (https://github.com/project-oak/rust-verification-tools/blob/main/verification-annotations/src/traits.rs).

The following functions should be provided:
```rust
pub fn assert(exp: bool) -> ();
pub fn assume(exp: bool) -> ();
```

The following trait is used for specifying non-deterministic values for types.
```rust
pub trait VerifierNonDet {
    // Create a basic non-deterministic value
    fn nondet(self) -> Self;

    // Create a non-deterministic value constrained by F.
    // Effectively combining verifier::nondet and verifier::assume
    fn nondet_where<F: FnOnce(&Self) -> bool>(f: F) -> Self;
}
```
It is currently expected that all types should implement this trait manually.

```rust
use crate::verifier::*;

fn main() {
    let x: u32 = verifier::nondet_where(|a| a < 10>);
    let y = verifier::nondet_where(|&x| (x*x)%2 == 0);
    let z = x*y;
    verifier::assert(z >= 0);
}
