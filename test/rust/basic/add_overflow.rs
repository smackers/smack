#[macro_use]
extern crate smack;
use smack::*;

// @flag --check=integer-overflow
// @expect error

fn main() {
    let a = 200u8.verifier_nondet();
    let b = 56u8.verifier_nondet();
    let c = a + b;
}
