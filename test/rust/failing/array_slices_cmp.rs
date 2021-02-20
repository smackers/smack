#[macro_use]
extern crate smack;
use smack::*;

// see: https://github.com/smackers/smack/issues/575
// @expect verified

fn main() {
    let ar = [
        2u8.verifier_nondet(),
        3u8.verifier_nondet(),
        4u8.verifier_nondet(),
        5u8.verifier_nondet(),
    ];
    smack::assume!(ar[0] == ar[2]);
    smack::assume!(ar[1] == ar[3]);
    let fh = &ar[0..2];
    let sh = &ar[2..4];
    smack::assert!(fh == sh);
}
