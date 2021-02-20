#[macro_use]
extern crate smack;
use smack::*;

// @expect error

struct NaN;

fn checked_addition(l: u8, r: u8) -> Result<u8, NaN> {
    let s = l + r;
    if s > 254 {
        Err(NaN)
    } else {
        Ok(s)
    }
}

fn main() {
    let a = 1u8.verifier_nondet();
    let b = 2u8.verifier_nondet();
    smack::assume!(a <= 128);
    smack::assume!(b < 128);
    let r = checked_addition(a, b);
    smack::assert!(r.is_ok() && r.unwrap_or(255) < 255);
}
