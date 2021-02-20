#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

fn fac(n: u64, acc: u64) -> u64 {
    match n {
        0 => acc,
        _ => fac(n - 1, acc * n),
    }
}

fn main() {
    let x = fac(5, 1);
    smack::assert!(x == 120);
}
