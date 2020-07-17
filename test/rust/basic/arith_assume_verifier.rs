#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

fn main() {
    let a = 6i32.verifier_nondet();
    let b = 7i32.verifier_nondet();
    verifier_assume!(4 < a && a < 8); // a in [5,7]
    verifier_assume!(5 < b && b < 9); // b in [6,8]
    verifier_assert!(30 <= a * b && a * b <= 56); // a*b in [30,56]
}
