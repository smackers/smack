#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn main() {
    let a = 6i32.verifier_nondet();
    let b = 7i32.verifier_nondet();
    verifier_assume!(4 < a && a < 8); // a in [5,7]
    verifier_assume!(5 < b && b < 9); // b in [6,8]
    let x = a * b;
    verifier_assert!(
        !(x == 30 || x == 35 || x == 40 || x == 36 || x == 48 || x == 42 || x == 49 || x == 56)
    ); // a*b != anything allowed
}
