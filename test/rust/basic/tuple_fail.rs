#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn main() {
    let t = (2u8.verifier_nondet(), 3u8.verifier_nondet());
    let (a, b) = t;
    smack::assume!(a < 4);
    smack::assume!(b < 5);
    smack::assert!(t.0 + t.1 < 7);
}
