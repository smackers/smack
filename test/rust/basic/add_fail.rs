#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn main() {
    let a = 2;
    let b = 3;
    smack::assert!(a + b != 5);
}
