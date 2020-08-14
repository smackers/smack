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
    let idx = 5usize.verifier_nondet();
    smack::assume!(idx < 3);
    let fh = &ar[..idx];
    let sh = &ar[idx..];
    smack::assert!(fh.len() + sh.len() == ar.len());
}
