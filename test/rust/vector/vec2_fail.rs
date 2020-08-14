#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn main() {
    let mut x: Vec<u64> = Vec::new();
    let mut y: Vec<u64> = Vec::new();
    x.push(0);
    y.push(0);
    smack::assert!(x[0] != y[0]);
}
