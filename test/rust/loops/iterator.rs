#[macro_use]
extern crate smack;
use smack::*;

// @flag --unroll=4
// @expect verified

fn fac(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        _ => n * fac(n - 1),
    }
}

fn main() {
    let mut a = 1;
    let n = 6u64.verifier_nondet();
    smack::assume!(n < 5);
    for i in 1..n + 1 as u64 {
        a *= i;
    }
    smack::assert!(a == fac(n)); // a == 6!
}
