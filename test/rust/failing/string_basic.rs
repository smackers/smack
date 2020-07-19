#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

fn main() {
    let s = String::from("Hello, world!");
    smack::assert!(s.capacity() >= 5);
}
