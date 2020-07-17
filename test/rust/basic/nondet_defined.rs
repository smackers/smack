#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

fn main() {
    // Verifies that nondet is defined in the ll file.
    let a = 6u32.verifier_nondet();
    verifier_assert!(a >= 0); // a is unsigned
}
