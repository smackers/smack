#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn main() {
    let mut ar = [
        2u8.verifier_nondet(),
        3u8.verifier_nondet(),
        4u8.verifier_nondet(),
    ];
    let idx = 1usize.verifier_nondet();
    smack::assume!(ar[0] < 4);
    smack::assume!(ar[1] < 5);
    smack::assume!(ar[2] < 6);
    smack::assume!(idx < 3 && idx > 1);
    let slice = &mut ar[..idx];
    slice[1] += 1;
    smack::assert!(slice.is_empty() || slice[1] < 5);
}
