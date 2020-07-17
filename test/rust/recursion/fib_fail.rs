#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn fib(x: u64) -> u64 {
    match x {
        0 => 1,
        1 => 1,
        _ => fib(x - 1) + fib(x - 2),
    }
}

fn main() {
    let x = fib(6);
    smack::assert!(x != 13);
}
