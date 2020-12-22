#[macro_use]
extern crate smack;
use smack::*;

// @expect verified
// @flag --float

fn main() {
    let a = 6.0f32.verifier_nondet();
    let b = 7.0f32.verifier_nondet();
    smack::assume!(a >= 0.0 && a <= 1.0);
    smack::assume!(b == b);
    smack::assert!(a + b >= b);
}
