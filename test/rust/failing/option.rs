#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

fn safe_div(x: u64, y: u64) -> Option<u64> {
    if y != 0 {
        Some(x / y)
    } else {
        None
    }
}

fn main() {
    let x = 2u64.verifier_nondet();
    smack::assume!(x > 0);
    let a = safe_div(2 * x, x);
    match a {
        Some(x) => smack::assert!(x == 2),
        None => smack::assert!(false),
    };
    let b = safe_div(x, 0);
    match b {
        Some(x) => smack::assert!(false),
        None => smack::assert!(true),
    };
}
