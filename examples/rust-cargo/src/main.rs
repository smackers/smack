#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn main() {
    let a: u32 = 2.verifier_nondet();
    let b: u32 = 3.verifier_nondet();
    smack::assert!(a + b != 5);
}
