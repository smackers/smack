#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn checked_addition(l: u8, r: u8) -> Option<u8> {
    let s = l + r;
    if s > 254 {
        None
    } else {
        Some(s)
    }
}

fn main() {
    let a = 1u8.verifier_nondet();
    let b = 2u8.verifier_nondet();
    smack::assume!(a < 128);
    smack::assume!(b < 127);
    let r = checked_addition(a, b);
    smack::assert!(r.is_none());
}
