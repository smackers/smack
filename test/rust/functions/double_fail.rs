#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn double(a: u32) -> u32 {
    a * 2
}

fn main() {
    let a = 2u32.verifier_nondet();
    let b = double(a);
    smack::assert!(b != 2 * a);
}
