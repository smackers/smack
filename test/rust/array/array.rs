#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

fn main() {
    let ar = [
        2u8.verifier_nondet(),
        3u8.verifier_nondet(),
        4u8.verifier_nondet(),
    ];
    let idx = 1usize.verifier_nondet();
    smack::assume!(ar[0] < 4);
    smack::assume!(ar[1] < 5);
    smack::assume!(ar[2] < 6);
    smack::assume!(idx < 3);
    smack::assert!(ar[idx] <= 5);
}
