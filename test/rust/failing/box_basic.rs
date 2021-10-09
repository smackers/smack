// fail reason: potential incompleteness of the solver
// https://github.com/smackers/smack/commit/195bd52ff351bd289a47f565ad3b0e2f14d25dcd
#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

fn main() {
    let b1: Box<i32> = Box::new(1);
    let b2: Box<i32> = Box::new(2);
    smack::assert!(*b1 != *b2);
}
