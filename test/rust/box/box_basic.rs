#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

fn main() {
    let b1: Box<i32> = Box::new(1);
    let b2: Box<i32> = Box::new(2);
    smack::assert!(*b1 != *b2);
}
